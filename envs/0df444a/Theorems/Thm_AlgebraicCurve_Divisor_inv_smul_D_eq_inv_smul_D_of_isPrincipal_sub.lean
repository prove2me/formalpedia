-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
-- name    : AlgebraicCurve.Divisor.inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/b4af3e84-097f-5fbd-8daa-79b93b5b763e
-- title:
--   Well-definedness of Serre's dlog map on p-torsion
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $p$ be a natural number for which $K$ has characteristic $p$ in the sense of `CharP`. A place of $F/K$ is a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and a principal ideal ring; for such a place $v$ and $f \in F$, $v.\mathrm{ord}\,f$ is the integer obtained as minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to $v$, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Assume the constants hypothesis: every nonzero $u \in F$ with $v.\mathrm{ord}\,u = 0$ at every place $v$ lies in the range of the structure map $K \to F$. Let $D_1, D_2$ be divisors such that $D_1 - D_2$ is principal, i.e. there is a nonzero $h \in F$ with $(D_1 - D_2)(v) = v.\mathrm{ord}\,h$ for all $v$. Let $f_1, f_2 \in F$ be nonzero and satisfy $p \cdot D_i(v) = v.\mathrm{ord}\,f_i$ for every place $v$, $i = 1,2$. Then $f_1^{-1} \cdot \mathrm{d}f_1 = f_2^{-1} \cdot \mathrm{d}f_2$ in the module of Kähler differentials of $F$ over $K$, the differentials being the values of `KaehlerDifferential.D K F` and the scaling being the $F$-action.
--
--   This is the well-definedness half of Serre's logarithmic differential map $\mathrm{Pic}^0(F/K)[p] \to \Omega_{F/K}$, $[D] \mapsto \mathrm{d}f/f$ where $pD = \mathrm{div}(f)$: the logarithmic differential depends only on the class of $D$. It is used to produce the injective homomorphism from $p$-torsion of $\mathrm{Pic}^0$ into differentials, and thence in the analysis of Fourier coefficients of modular forms on the modular curve side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
    (K F : Type*) [Field K] [Field F] [Algebra K F] (p : ℕ) [CharP K p]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : AlgebraicCurve.Place K F, v.ord u = 0) →
      u ∈ (algebraMap K F).range)
    (D₁ D₂ : AlgebraicCurve.Divisor K F) (h : AlgebraicCurve.Divisor.IsPrincipal (D₁ - D₂))
    (f₁ f₂ : F) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₁ v = v.ord f₁)
    (h₂ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
    f₁⁻¹ • KaehlerDifferential.D K F f₁ = f₂⁻¹ • KaehlerDifferential.D K F f₂ := by sorry
