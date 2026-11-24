-- Prove2me | Theorems.Thm_Arxiv1606_07694_small_slope_equivalence
-- name    : Arxiv1606_07694.small_slope_equivalence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:41:13.788803+00:00
-- url     : https://prove2.me/theorems/8c3f8be5-96ae-4cf6-b730-d3707bab3a96
-- title:
--   Eqs. (26)-(33) (as proved): the resummed amplitude agrees with Voronovich's small-slope ansatz to order $(\nabla h)^2$
-- statement:
--   Assume symmetric kernels with reduced expansions (19), and the recursion (15) for $n=1,2$ as an identity of functions. Let $h$ be a real Schwartz height profile, fix $\mathbf k,\mathbf k_0$ with $q\ne0$, $q_0\ne0$ and $q+q_0\ne0$. Define Voronovich's kernels by the dictionary (28) and (29): $B^{11}=A^{(1)}/(2i\sqrt{qq_0})$ and $B_2^{11}(\mathbf k,\mathbf k_0;\mathbf k_1)=\tilde G^{(2)}(\mathbf k-\mathbf k_1,\mathbf k_1-\mathbf k_0;\mathbf k,\mathbf k_0)/(2\sqrt{qq_0})$, with $\tilde G^{(2)}$ in its second-order form $A^{(2)}-D^{(2)}_{\mu\nu}\mathbf k_1^\mu\mathbf k_2^\nu$. Let $M^{11}$ be given by (27). Then the two bracketed terms of Voronovich's ansatz (26) equal those of (25):
--
--   1. $\dfrac{2\sqrt{qq_0}}{q+q_0}\,B^{11}(\mathbf k,\mathbf k_0)=\dfrac{A^{(1)}(\mathbf k,\mathbf k_0)}{i(q_0+q)}$;
--   2. with $\tilde h_V(\mathbf k_1)=(2\pi)^{-2}\int h\,e^{-i\mathbf k_1\cdot\mathbf x}$,
--   $$\frac{2\sqrt{qq_0}}{q+q_0}\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h]}\Big(-\frac i4\Big)\int d^2\mathbf k_1\,M^{11}(\mathbf k,\mathbf k_0;\mathbf k_1)\tilde h_V(\mathbf k_1)e^{i\mathbf k_1\cdot\mathbf x}=\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h]}\,\tfrac12D^{(2)}_{\mu\nu}\,\partial_\mu h\,\partial_\nu h.\qquad(33)$$
--
--   So, to order $(\nabla h)^2$, the resummed amplitude (25) coincides with the small-slope approximation, which gives a derivation of Voronovich's ansatz.
--
--   **Formalization Note** The first terms of (25) and (26) are constants (in $\mathbf x$) times the same integral $\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h]}$. This integral is a distribution, $(2\pi)^2\delta^{(2)}(\mathbf k-\mathbf k_0)$ plus the regular function $\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}(e^{i(q+q_0)h}-1)$. Their equality is therefore stated as equality of the coefficients. Eq. (29) is printed with a garbled argument list. For $n=1$, the only case used, it reads $\tilde G^{(2)}(\mathbf k-\mathbf k_1,\mathbf k_1-\mathbf k_0)$. Eq. (32) holds with $\tilde h$ in Voronovich's normalization $(2\pi)^{-2}\int h\,e^{-i\mathbf k\cdot\mathbf x}$, and with the standard one it is off by $(2\pi)^2$. The recursion (22) with $m=1$, which the proof uses, needs (15) off the hyperplane, hence "(as proved)". $\sqrt{qq_0}$ is the principal square root; it cancels from the identities.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c011; Section "Comparison with Voronovich's small-slope approximation", eqs. (26)-(32) PDF p. 4, eq. (33) PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem small_slope_equivalence (G : KernelFamily) (A : ℕ → Vec2 → Vec2 → ℂ)
    (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ) (qv : Vec2 → ℂ)
    (hG : IsSymmetricKernel G)
    (h19 : ∀ (n : ℕ) (k k0 : Vec2), HasReducedExpansion (G n k k0) (A n k k0) (D n k k0))
    (h15 : ∀ (n m : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2), 1 ≤ n → n ≤ 2 →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ)
    (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2)
    (hq : qv k + qv k0 ≠ 0) (hqk : qv k ≠ 0) (hqk0 : qv k0 ≠ 0) :
    2 * sqrtqq0 qv k k0 / (qv k + qv k0) * voronovichB11 A qv k k0 = A 1 k k0 / shiftFactor qv k k0 ∧
      ssaSecondTerm A D qv h k k0 = curvatureTerm (D 2 k k0) qv h k k0 := by sorry

end Arxiv1606_07694
