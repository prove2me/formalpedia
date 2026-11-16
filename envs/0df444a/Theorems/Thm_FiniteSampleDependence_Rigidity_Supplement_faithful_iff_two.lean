-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_faithful_iff_two
-- name    : FiniteSampleDependence.Rigidity.Supplement.faithful_iff_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:50:00.255535+00:00
-- url     : https://prove2.me/theorems/622322f6-ff1a-431b-875d-6ae6a1117302
-- title:
--   Theorem 5.1 — an independence-faithful $C^1$-extendable (LF-DPI), (IZ) functional exists iff $n=2$; for $n=2$ the Gram determinant is one
-- statement:
--   Let $n,m\ge2$. Call a functional $F$ on $\Delta_{n,m}$ *independence-faithful* if, for $U\in\Delta_{n,m}$, $F(U)=0$ exactly when $\operatorname{rank}U=1$. Then:
--
--   1. there exists an independence-faithful, $C^1$-extendable functional on $\Delta_{n,m}$ satisfying (LF-DPI) and (IZ) if and only if $n=2$;
--   2. when $n=2$, the Gram determinant
--   $$F_{\mathrm{Gram}}(U)=\det(UU^\top)$$
--   is such a functional: it is independence-faithful, $C^1$-extendable, and satisfies (LF-DPI) and (IZ).
--
--   The functional in clause 1 is arbitrary (not required to be a polynomial). The theorem says that faithful detection of independence by a boundary-regular dependence measure obeying the data processing inequality is possible exactly when the processed alphabet is binary.
--
--   Differences from the source:
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function on all real n×m matrices, of which only the values on Δ_{n,m} enter; reason: every hypothesis and conclusion reads F only at points of Δ_{n,m} (TU stays in Δ_{n,m}); every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the Gram determinant det(UUᵀ) → polyFun (gramPoly n m), the published polynomial whose value at U is det(UUᵀ); reason: the published sanity lemma polyFun_gramPoly identifies the two
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem 5.1, PDF p. 15 (printed p. 14); independence-faithful defined in §5.1, same page

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Theorem 5.1 (Faithfulness exactly when `n = 2`), PDF p. 15 (printed p. 14). For `n, m ≥ 2`,
an independence-faithful, `C¹`-extendable functional on `Δ_{n,m}` satisfying (LF-DPI) and (IZ)
exists if and only if `n = 2`; when `n = 2` the Gram determinant `det(UUᵀ)` is such a
functional. -/
theorem faithful_iff_two {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ((∃ F : Matrix (Fin n) (Fin m) ℝ → ℝ,
        IndependenceFaithful F ∧ IsC1Extendable F ∧ LFDPI F ∧ IZ F) ↔ n = 2) ∧
    (n = 2 →
      IndependenceFaithful (polyFun (gramPoly n m)) ∧ IsC1Extendable (polyFun (gramPoly n m)) ∧
        LFDPI (polyFun (gramPoly n m)) ∧ IZ (polyFun (gramPoly n m))) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
