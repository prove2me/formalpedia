-- Prove2me | Theorems.Thm_Arxiv1606_07694_resummed_scattering_amplitude
-- name    : Arxiv1606_07694.resummed_scattering_amplitude
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:37:11.300958+00:00
-- url     : https://prove2.me/theorems/e9fc5efe-ded6-4a19-bfb6-41e93daccec0
-- title:
--   Eq. (25) (as proved): the resummed scattering amplitude to order $(\nabla h)^2$
-- statement:
--   Assume the hypotheses of Eqs. (21) to (24) (as proved): symmetric kernels with reduced expansions (19), the recursion (15) for $n=1,2$ as an identity of functions, (15) for $n=0$ on $\mathbf k=\mathbf k_0$, and $\tilde G^{(0)}(;\mathbf k_0,\mathbf k_0)=R(\mathbf k_0)$. Let $h$ be a real Schwartz height profile and fix $\mathbf k,\mathbf k_0$ with $q_0+q\ne0$ and $q_0\ne0$, and put $c=i(q_0+q)$. Replace every kernel in the series (8) by its second-order form $A^{(n)}-D^{(n)}_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu$. Then:
--
--   1. the terms of order $n\ge1$ form a convergent series, whose sum is
--   $$\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}\Big[\frac{A^{(1)}(\mathbf k,\mathbf k_0)}{i(q_0+q)}\big(e^{i(q+q_0)h(\mathbf x)}-1\big)+\tfrac12D^{(2)}_{\mu\nu}(\mathbf k,\mathbf k_0)\,\partial_\mu h\,\partial_\nu h\,e^{i(q+q_0)h(\mathbf x)}\Big];$$
--   2. the coefficient of $(2\pi)^2\delta^{(2)}(\mathbf k_0-\mathbf k)$ vanishes: $R(\mathbf k_0)-A^{(1)}(\mathbf k_0,\mathbf k_0)/(2iq_0)=0$.
--
--   Together, 1 and 2 say that the series with second-order kernels equals
--   $$S(\mathbf k,\mathbf k_0)=\int d^2\mathbf x\,e^{i[(\mathbf k_0-\mathbf k)\cdot\mathbf x+(q+q_0)h(\mathbf x)]}\Big[\frac{A^{(1)}(\mathbf k,\mathbf k_0)}{i(q_0+q)}+\tfrac12D^{(2)}_{\mu\nu}(\mathbf k,\mathbf k_0)\,\partial_\mu h\,\partial_\nu h\Big],\qquad(25)$$
--   where $\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}=(2\pi)^2\delta^{(2)}(\mathbf k_0-\mathbf k)$. This is the derivative expansion of the scattering amplitude, resummed to all orders in the height and truncated at second order in its derivatives. It is the paper's main result.
--
--   **Formalization Note** Eq. (25) contains the non-integrable integral $\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}A^{(1)}/c$, which is a delta function. The Lean statement therefore splits (25), and the series, into a function of $\mathbf k$ (part 1, stated with `HasSum` for every $\mathbf k$) and the coefficient of the delta function (part 2). The vertical-shift recursion for $n=1,2$ is assumed off the hyperplane, as in Eqs. (21) to (24) (as proved), because the paper's derivation needs it. The relation between the true amplitude and the series with truncated kernels, which the paper calls valid "to order $(\nabla h)^2$", is not quantified in the paper and is not part of the statement.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c010; Section "Resummation of the perturbative series", eq. (20) PDF p. 3, eq. (25) and the display before it, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem resummed_scattering_amplitude (G : KernelFamily) (A : ℕ → Vec2 → Vec2 → ℂ)
    (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ) (R qv : Vec2 → ℂ)
    (hG : IsSymmetricKernel G)
    (h19 : ∀ (n : ℕ) (k k0 : Vec2), HasReducedExpansion (G n k k0) (A n k k0) (D n k k0))
    (h15 : ∀ (n m : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2), 1 ≤ n → n ≤ 2 →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ)
    (h15zero : ∀ (m : ℕ) (k0 : Vec2), G m k0 k0 0 = shiftFactor qv k0 k0 ^ m * G 0 k0 k0 0)
    (h7 : ∀ k0 : Vec2, G 0 k0 k0 0 = R k0)
    (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2) (hq : qv k0 + qv k ≠ 0) (hq0 : qv k0 ≠ 0) :
    HasSum (fun m : ℕ => seriesTerm h k k0 m (truncKernel A D (m + 1) k k0))
        (resummedRegular A D qv h k k0) ∧
      R k0 - A 1 k0 k0 / (2 * I * qv k0) = 0 := by sorry

end Arxiv1606_07694
