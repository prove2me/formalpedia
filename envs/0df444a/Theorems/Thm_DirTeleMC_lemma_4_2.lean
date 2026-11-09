-- Prove2me | Theorems.Thm_DirTeleMC_lemma_4_2
-- name    : DirTeleMC.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:14.024493+00:00
-- url     : https://prove2.me/theorems/29ce7b3f-96c1-4a2a-9e7d-a9aa1fcb01f9
-- title:
--   Lemma 4.2 — height reduction with bounded vertex loads
-- statement:
--   **Lemma 4.2.** Let $T$ be an out-arborescence of $G$ rooted at $s$ that contains a set $K$ of $k = |K| \ge 2$ terminals ($s \notin K$), with height at most $\theta$ and maximum out-degree at most $d$. For every integer $\ell \ge 1$ let $\rho = \lceil k^{1/\ell}\rceil$. There is a jump arborescence $J$ for $K$ of depth at most $2\ell - 1$, with jumps of at most $\theta$ arcs, all of whose jumps are (possibly empty) directed paths in $T$, such that
--   $$\Lambda(J) \le (\ell - 1)\max\{d, \rho - 1\} + \rho.$$
--
--   Applied to the arborescence of a short schedule, the lemma shows that a shallow jump arborescence with small loads exists; the greedy algorithm is compared with it.
--
--   Differences from the source:
--   - encoding: the terminal set K with k = |K| → a parameter set Y with |Y| = k ≥ 2 and s ∉ Y; reason: the proof of Theorem 1.1 (p.31) applies the lemma to the k informed terminals; s ∉ Y is the standing K ⊆ V \ {s}
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma 4.2, p.11 (PDF p.12); proof pp.23–24 (PDF pp.24–25)

import Mathlib
import Definitions.Def_DirTeleMC_IsJumpArb
import Definitions.Def_DirTeleMC_Arb
import Definitions.Def_DirTeleMC_rho

namespace DirTeleMC

/-- **Lemma 4.2** (height reduction with bounded vertex loads).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma 4.2, p.11 (restated p.23): "Let T be an out-arborescence rooted at s that contains K, with
k = |K| ≥ 2, height at most θ, and maximum out-degree at most d. For every integer ℓ ≥ 1, let ρ = ⌈k^{1/ℓ}⌉.
There is a jump arborescence J of depth at most 2ℓ − 1, whose jumps are (possibly empty) directed paths in T,
such that Λ(J) ≤ (ℓ − 1) max{d, ρ − 1} + ρ."

For every out-arborescence `T` of `G` rooted at `s` that contains a terminal set `Y` with `|Y| = k ≥ 2` and
`s ∉ Y`, of height at most `θ` and maximum out-degree at most `d`, and every `ℓ ≥ 1`, there is a jump
arborescence `J` for `Y` (Definition 4.1, with jumps of at most `θ` arcs) of depth at most `2ℓ − 1`, all of
whose jumps are directed paths of `T`, with `Λ(J) ≤ (ℓ − 1) max{d, ρ − 1} + ρ`, `ρ = ⌈k^{1/ℓ}⌉`.

**Formalization Note.** The terminal set is a parameter `Y` (the paper's `K`; p.31 applies the lemma to the
`k` informed terminals for k-multicast). `s ∉ Y` is the standing `K ⊆ V \ {s}` (§1). `ρ ≥ 2` as `k ≥ 2`, so
`ρ − 1` is not truncated; `ℓ − 1` is not truncated as `ℓ ≥ 1`. -/
theorem lemma_4_2 {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) (T : Arb n) (hT : T.IsIn adj)
    (hroot : T.root = s) (Y : Finset (Fin n)) (hsY : s ∉ Y) (hY : Y ⊆ T.verts) (hk : 2 ≤ Y.card)
    (θ d : ℕ) (hθ : T.height ≤ θ) (hd : T.OutDegLE d) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ J : JTree n, JTree.IsJumpArb adj θ (2 * ℓ - 1) s Y J ∧
      J.AllJumps (fun u P w => T.IsTreePath u P w) ∧
      J.maxLoad ≤ (ℓ - 1) * max d (rho Y.card ℓ - 1) + rho Y.card ℓ := by sorry

end DirTeleMC
