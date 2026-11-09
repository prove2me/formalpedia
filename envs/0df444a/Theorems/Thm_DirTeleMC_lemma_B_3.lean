-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_3
-- name    : DirTeleMC.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:34:11.381036+00:00
-- url     : https://prove2.me/theorems/c55d9611-61dd-4900-b022-50536436358c
-- title:
--   Lemma B.3 — the fallback schedule informs $Y$ within OPT $+ k$ rounds
-- statement:
--   **Lemma B.3.** Let $(G, s, K, k)$ be a well-formed instance and $Y$ its set of terminals (for $k$-multicast, the $k$ terminals nearest to $s$). The busy schedule along a shortest-path out-arborescence from $s$ to $Y$ (line 2 of Algorithm 2) exists; for every choice of the $k$ nearest terminals $Y$, of the pruned shortest-path out-arborescence and of the child order, it is valid, informs every terminal of $Y$ (hence $k$ terminals), and its length is at most
--   $$\mathrm{OPT} + k;$$
--   in particular it is at most $2\,\mathrm{OPT}$ when $\mathrm{OPT} \ge k$. Here OPT is the length of any valid schedule informing $k$ terminals, and the bound holds for each such schedule.
--
--   Differences from the source:
--   - encoding: OPT, the minimum number of rounds → every valid schedule S′ informing k terminals, with T′ its length; reason: the same claim without a minimum over a possibly empty set
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.3, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_FallbackRun

namespace DirTeleMC

/-- **Lemma B.3** (the fallback schedule).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.3, p.26: "Let Y be the set of terminals (for k-multicast, the k terminals nearest to s). The busy
schedule along a shortest-path out-arborescence from s to Y, computed in line 2 of Algorithm 2, informs Y within
OPT + k rounds. In particular it is a 2-approximation when OPT ≥ k."

For a well-formed instance, a fallback schedule exists; and for every set `Y` of `k` terminals nearest to `s`,
every shortest-path out-arborescence `A` from `s` pruned to `Y` and every child order (every run of line 2 of
Algorithm 2), the busy schedule along `A` is valid, informs every terminal of `Y` (so `k` terminals), and for
every valid schedule `S′` of length `T′` informing `k` terminals has length at most `T′ + k`, and at most `2T′`
when `T′ ≥ k`.

**Formalization Note.** OPT is written as "every valid schedule `S′` informing `k` terminals", so no minimum
over a possibly empty set is taken. The run is unpacked into the data of `FallbackRun` (`Y`, `A`, `ord`), so that
"informs Y" can name the set `Y`. -/
theorem lemma_B_3 (I : Inst) (hI : I.WF) :
    (∃ S, FallbackRun I S) ∧
    ∀ (Y : Finset (Fin I.n)) (A : Arb I.n) (ord : Fin I.n → List (Fin I.n)),
      Y ⊆ I.K → Y.card = I.k → (∀ y ∈ Y, ∀ t ∈ I.K \ Y, dist I.adj I.s y ≤ dist I.adj I.s t) →
      IsPrunedSPT I.adj I.s Y A → A.IsChildOrder ord →
      (A.arbSchedule ord).Valid I ∧
        Y ⊆ informedAfter I.s (A.arbSchedule ord) (A.arbSchedule ord).length ∧
        (A.arbSchedule ord).InformsK I ∧
        ∀ S' : Schedule I.n, S'.Valid I → S'.InformsK I →
          (A.arbSchedule ord).length ≤ S'.length + I.k ∧
            (I.k ≤ S'.length → (A.arbSchedule ord).length ≤ 2 * S'.length) := by sorry

end DirTeleMC
