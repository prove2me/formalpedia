-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_5_3
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:22:38.657205+00:00
-- url     : https://prove2.me/theorems/e01d7931-faea-445a-be0f-ee15035950d1
-- title:
--   Lemma 5.3 — Full action-defect inequality
-- statement:
--   Let $G,H$ be nonempty finite sets of equal size, with a group structure on $H$, an arbitrary operation $*$ on $G$, and arbitrary visible signed labels $u_j$. Choose $k>0$ marks $a_i\in H$, a partial map $\Psi:G\rightharpoonup H$, and any positive conductance lower bound $\Phi$ for the marked Cayley multigraph. Then
--   $$\operatorname{defect}(\Psi)\le\frac{1+\Phi}{\Phi}\eta_{\rm act}(\Psi).$$
--   The action failure rate includes undefined values, the forward multiplication comparison, and the reverse query $(x*u_j)*u_{-j}=x$. No permutation or inverse promise is imposed on the visible maps. The statement covers both image-size regimes in the proof.
--
--   Differences from the source:
--   - encoding: normalized minimum conductance at least Phi>0 → the corresponding boundary inequality for every nonempty set of size at most half; reason: multiplicities are retained and k>0 makes the normalization nonzero
--   - generalization: the nontrivial-size candidate Cayley graphs of the tester → all equal-size nonempty finite carriers, including size one; reason: at size one the boundary condition is vacuous, but defect is zero for a defined map and one for an undefined map, whose action failure rate is one
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 31, Lemma 5.3

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_5_3 {G H : Type} [Fintype G] [Fintype H] [Nonempty G]
    [Group H] (hcard : Fintype.card G = Fintype.card H) {k : ℕ} (hk : 0 < k)
    (op : G → G → G) (u : Signed k → G) (a : Fin k → H) (ψ : PartialMap G H)
    (Φ : ℝ) (hΦ : 0 < Φ) (hexp : ConductanceAtLeast a Φ) :
    defect ψ ≤ ((1 + Φ) / Φ) * etaAct op u a ψ := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
