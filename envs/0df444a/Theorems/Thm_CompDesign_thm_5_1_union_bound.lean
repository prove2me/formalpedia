-- Prove2me | Theorems.Thm_CompDesign_thm_5_1_union_bound
-- name    : CompDesign.thm_5_1_union_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:52:50.786077+00:00
-- url     : https://prove2.me/theorems/0e74526c-cc23-4dd6-b6d0-f4cff803c0b1
-- title:
--   Proof of Theorem 5.1 — $v(T)\le v(S\cup T)\le v(S)+\sum_{i\in T\setminus S}(v(S\cup\{i\})-v(S))$
-- statement:
--   Let $v:2^N\to\mathbb R$ satisfy Assumption 3.1: $v(\emptyset)=0$, monotone and submodular. For all $S,T\subseteq N$,
--   $$v(T)\le v(S\cup T)\le v(S)+\sum_{i\in T\setminus S}\big(v(S\cup\{i\})-v(S)\big).$$
--
--   The first inequality is monotonicity; the second is the standard consequence of submodularity that the gain of adding a set is at most the sum of the single-element gains. The proof of Theorem 5.1 applies it with $S$ an equilibrium and $T$ an optimal set.
--
--   Differences from the source:
--   - generalization: S a pure Nash equilibrium of Γ^mc and T = S* ∈ arg max{v(T) : ∑_{i∈T} c_i ≤ B} → arbitrary sets S, T; reason: the printed inequalities use only monotonicity and submodularity; the paper's S and S* are an instance
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 5.1, §5.1, p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF

open CompDesignBFM

namespace CompDesign

/-- The submodular union bound, proof of Theorem 5.1, §5.1, p.27 (PDF 30) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
by monotonicity and submodularity, `v(T) ≤ v(S ∪ T) ≤ v(S) + ∑_{i∈T∖S} (v(S ∪ {i}) − v(S))`.

**Formalization Note.** The proof uses it with `S` an equilibrium and `T = S*` an optimal set; it is
stated for all `S, T`. Assumption 3.1 is kept as binders. -/
theorem thm_5_1_union_bound {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0)
    (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (S T : Finset (Fin n)) :
    v T ≤ v (S ∪ T) ∧ v (S ∪ T) ≤ v S + ∑ i ∈ T \ S, (v (insert i S) - v S) := by sorry

end CompDesign
