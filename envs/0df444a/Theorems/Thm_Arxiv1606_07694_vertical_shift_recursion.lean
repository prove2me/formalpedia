-- Prove2me | Theorems.Thm_Arxiv1606_07694_vertical_shift_recursion
-- name    : Arxiv1606_07694.vertical_shift_recursion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T23:22:22.327617+00:00
-- url     : https://prove2.me/theorems/7ca3e183-b749-4a51-ad1b-6741358c4976
-- title:
--   Eq. (15): the recursion for the reduced kernels from vertical-shift invariance
-- statement:
--   Fix in-plane wave vectors $\mathbf k,\mathbf k_0$, write $c=i(q_0+q)$, and let $\tilde G^{(n)}$ ($n\ge0$) be symmetric reduced kernels. Suppose the vertical-shift identities (14) hold: for every $n\ge0$, every $p\ge1$ and every $(\mathbf k_1,\dots,\mathbf k_n)\in\mathcal P^{(n)}$,
--   $$\sum_{j=0}^{p}(-1)^j\binom pj c^{\,p-j}\,\tilde G^{(n+j)}(\mathbf k_1,\dots,\mathbf k_n,\underbrace{\mathbf 0,\dots,\mathbf 0}_{j};\mathbf k,\mathbf k_0)=0.$$
--   Then for all $n,m\ge0$ and all $(\mathbf k_1,\dots,\mathbf k_n)\in\mathcal P^{(n)}$,
--   $$\tilde G^{(n+m)}(\mathbf k_1,\dots,\mathbf k_n,\underbrace{\mathbf 0,\dots,\mathbf 0}_{m};\mathbf k,\mathbf k_0)=c^{m}\,\tilde G^{(n)}(\mathbf k_1,\dots,\mathbf k_n;\mathbf k,\mathbf k_0).\qquad(15)$$
--
--   This recursion is the input to the resummation of the perturbative series.
--
--   **Formalization Note** The statement covers the paper's step from (14) to (15) ("solved iteratively"). The common factor $(2\pi)^2\delta^{(2)}(\mathbf k_1+\dots+\mathbf k_n+\mathbf k_0-\mathbf k)$ of (14) is removed by restricting to $\mathcal P^{(n)}$. The derivation of (14) from the power series (4) and the shift invariance (9) is not formalized, because the paper does not specify the function spaces or convergence of the series. Polarization indices are suppressed.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c001; Section "Perturbative expansion of the SA", eqs. (14)-(15), PDF p. 3 (eqs. (9)-(13) on p. 2)

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem vertical_shift_recursion (G : KernelFamily) (hG : IsSymmetricKernel G)
    (qv : Vec2 → ℂ) (k k0 : Vec2)
    (h14 : ∀ (n p : ℕ) (κ : Fin n → Vec2), 0 < p → OnHyperplane k k0 κ →
      ∑ j ∈ Finset.range (p + 1), (-1 : ℂ) ^ j * (p.choose j : ℂ) * shiftFactor qv k k0 ^ (p - j) *
        G (n + j) k k0 (Fin.append κ (0 : Fin j → Vec2)) = 0) :
    ∀ (n m : ℕ) (κ : Fin n → Vec2), OnHyperplane k k0 κ →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ := by sorry

end Arxiv1606_07694
