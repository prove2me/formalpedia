-- Prove2me | Theorems.Thm_Arxiv1606_07694_taylor_coefficient_recursions
-- name    : Arxiv1606_07694.taylor_coefficient_recursions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:29:47.427984+00:00
-- url     : https://prove2.me/theorems/342d2b87-24dd-4785-a51a-dd3c5f1b6ebe
-- title:
--   Eqs. (21)-(24) (as proved): recursions for the Taylor coefficients $A^{(n)}$ and $D^{(n)}$
-- statement:
--   Let $\tilde G^{(n)}$ be a symmetric kernel family and $q(\cdot)$ a vertical-wavenumber function, with $c(\mathbf k,\mathbf k_0)=i(q_0+q)$. Assume:
--
--   1. for every $n$, $\mathbf k$, $\mathbf k_0$, the kernel has the reduced expansion (19) with coefficients $A^{(n)}(\mathbf k,\mathbf k_0)$, $D^{(n)}_{\mu\nu}(\mathbf k,\mathbf k_0)$;
--   2. the recursion (15) holds for $n=1,2$ as an identity of functions: $\tilde G^{(n+m)}(\mathbf k_1,\dots,\mathbf k_n,\mathbf 0,\dots,\mathbf 0;\mathbf k,\mathbf k_0)=c^m\tilde G^{(n)}(\mathbf k_1,\dots,\mathbf k_n;\mathbf k,\mathbf k_0)$ for all $\mathbf k_1,\dots,\mathbf k_n$, all $m\ge0$, all $\mathbf k,\mathbf k_0$;
--   3. for $n=0$, (15) holds on $\mathcal P^{(0)}=\{\mathbf k=\mathbf k_0\}$: $\tilde G^{(m)}(\mathbf 0,\dots,\mathbf 0;\mathbf k_0,\mathbf k_0)=(2iq_0)^m\tilde G^{(0)}(;\mathbf k_0,\mathbf k_0)$;
--   4. $\tilde G^{(0)}(;\mathbf k_0,\mathbf k_0)=R(\mathbf k_0)$, the planar reflection coefficient (eq. 7).
--
--   Then for all $m\ge0$ and all $\mathbf k,\mathbf k_0$:
--   $$A^{(m)}(\mathbf k_0,\mathbf k_0)=(2iq_0)^mR(\mathbf k_0),\qquad A^{(m+1)}(\mathbf k,\mathbf k_0)=c^mA^{(1)}(\mathbf k,\mathbf k_0),$$
--   $$A^{(m+2)}(\mathbf k,\mathbf k_0)=c^mA^{(2)}(\mathbf k,\mathbf k_0),\qquad D^{(m+2)}_{\mu\nu}(\mathbf k,\mathbf k_0)=c^mD^{(2)}_{\mu\nu}(\mathbf k,\mathbf k_0).$$
--
--   These are eqs. (21) to (24), the coefficient relations used to sum the series.
--
--   **Formalization Note** The paper states (15) only on $\mathcal P^{(n)}$. Its derivation of (22) to (24) matches Taylor coefficients at $\mathbf k_1=\dots=\mathbf k_n=\mathbf 0$, a point that lies on $\mathcal P^{(n)}$ only when $\mathbf k=\mathbf k_0$. Hypothesis 2, (15) for $n=1,2$ off the hyperplane, is what that derivation uses. Without it, (22) to (24) do not follow for $\mathbf k\ne\mathbf k_0$. Hence the title "(as proved)".
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c005; Section "Resummation of the perturbative series", eqs. (21)-(23) PDF p. 3, eq. (24) PDF p. 4; uses eqs. (7), (15), (19)

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem taylor_coefficient_recursions (G : KernelFamily) (A : ℕ → Vec2 → Vec2 → ℂ)
    (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ) (R qv : Vec2 → ℂ)
    (hG : IsSymmetricKernel G)
    (h19 : ∀ (n : ℕ) (k k0 : Vec2), HasReducedExpansion (G n k k0) (A n k k0) (D n k k0))
    (h15 : ∀ (n m : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2), 1 ≤ n → n ≤ 2 →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ)
    (h15zero : ∀ (m : ℕ) (k0 : Vec2), G m k0 k0 0 = shiftFactor qv k0 k0 ^ m * G 0 k0 k0 0)
    (h7 : ∀ k0 : Vec2, G 0 k0 k0 0 = R k0) :
    (∀ (m : ℕ) (k0 : Vec2), A m k0 k0 = (2 * I * qv k0) ^ m * R k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), A (m + 1) k k0 = shiftFactor qv k k0 ^ m * A 1 k k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), A (m + 2) k k0 = shiftFactor qv k k0 ^ m * A 2 k k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), D (m + 2) k k0 = shiftFactor qv k k0 ^ m • D 2 k k0) := by sorry

end Arxiv1606_07694
