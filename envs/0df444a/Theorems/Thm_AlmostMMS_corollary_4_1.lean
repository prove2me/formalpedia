-- Prove2me | Theorems.Thm_AlmostMMS_corollary_4_1
-- name    : AlmostMMS.corollary_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:42.975694+00:00
-- url     : https://prove2.me/theorems/3b4f3f22-6c45-46b9-b39c-7b4280cfd644
-- title:
--   Corollary 4.1 — protected prefixes control all prefixes
-- statement:
--   Let $(U,V,W)$ partition $N$ and let $(W,S,\eta)$ have the saved-items property, with $E=M-S$ and $|V|\ge3n/4$. Let $A\subseteq V$ with choices $j_i$ be an output of Theorem 4.1 and $A_0\subseteq A$. Let $U_0\subseteq U$ carry head profiles $\pi^E_u$ with $|\pi^E_u|\le q$. If for every $\ell_s\in L_S$
--   $$
--   \sum_{i\in A_0}P_i(\pi^E_i,\ell_s)+\sum_{u\in U_0}P_u(\pi^E_u,\ell_s)\le|E\cap[\ell_s]|,
--   $$
--   and $|U_0|\le\eta/(3q)$, then the same inequality holds at every $0\le\ell\le m$.
--
--   Differences from the source:
--   - reading: "Given the sets W and S from Lemma 4.1", "the defined E, S and V" and "integral profiles", left to the context → explicit hypotheses: the partition, the saved-items property, |V| ≥ 3n/4, and head profiles of at most q demands; reason: the proof on pp.34–35 uses exactly these
--   - generalization: the specific sets of Lemma 4.1 and Definition 4.2 → any data with those properties; reason: the proof uses only the listed properties, and the source's sets have them
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Corollary 4.1, p.34

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_mmsProfileIn
import Definitions.Def_AlmostMMS_IsPartialSelection
import Definitions.Def_AlmostMMS_IsSavedSplit

namespace AlmostMMS

open Finset

/-- **Corollary 4.1, p.34.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `A ⊆ V` with profiles `π_i` be obtained from Theorem 4.1 for the
defined `E, S, V`, let `A₀ ⊆ A`, and let `U₀ ⊆ U` carry integral profiles `π_u`. If (E_{L_S}) holds at every
protected prefix and `|U₀| ≤ η/(3q)`, then for every `0 ≤ ℓ ≤ m`,
`∑_{i ∈ A₀} P_i(π^E_i, ℓ) + ∑_{u ∈ U₀} P_u(π^E_u, ℓ) ≤ |E ∩ [ℓ]|`.

**Formalization Note.** The context of the printed corollary is explicit: `(U, V, W)` is a partition of `N`,
`(W, S, η)` has the saved-items property, `|V| ≥ 3n/4` (Definition 4.2 and p.35), and `(A, j)` is any output
of partial selection. The `π^E_u` are head profiles with `|π^E_u| ≤ q`, which the proof uses on p.35. The
statement holds for any such data, not only those of Lemma 4.1 and Definition 4.2. -/
theorem corollary_4_1 {n m d q : ℕ} (hq : 3 ≤ q) (hd : 1 ≤ d) (J : OrderedInstance n m d)
    (U V W : Finset (Fin n)) (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (hcover : U ∪ V ∪ W = univ) (S : Finset (Fin m)) (η : ℕ) (hsaved : IsSavedSplit J.v q W S η)
    (hV : 3 * (n : ℝ) / 4 ≤ (V.card : ℝ)) (A : Finset (Fin n)) (j : Fin n → Fin d)
    (hA : IsPartialSelection J q S V A j) (A₀ : Finset (Fin n)) (hA₀ : A₀ ⊆ A)
    (U₀ : Finset (Fin n)) (hU₀ : U₀ ⊆ U) (πE : Fin n → Multiset ℝ)
    (hπE : ∀ u ∈ U₀, IsHeadProfile q (πE u) ∧ (πE u).card ≤ q)
    (hELS : ∀ ℓs ∈ protectedPrefixes S,
      ∑ i ∈ A₀, load J.v i (mmsProfileIn J q i (j i) Sᶜ) ℓs + ∑ u ∈ U₀, load J.v u (πE u) ℓs ≤
        prefixCount Sᶜ ℓs)
    (hU₀η : (U₀.card : ℝ) ≤ (η : ℝ) / (3 * (q : ℝ))) :
    ∀ ℓ ≤ m,
      ∑ i ∈ A₀, load J.v i (mmsProfileIn J q i (j i) Sᶜ) ℓ + ∑ u ∈ U₀, load J.v u (πE u) ℓ ≤
        prefixCount Sᶜ ℓ := by sorry

end AlmostMMS
