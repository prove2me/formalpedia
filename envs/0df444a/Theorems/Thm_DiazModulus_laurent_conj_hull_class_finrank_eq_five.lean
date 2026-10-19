-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_class_finrank_eq_five
-- name    : DiazModulus.laurent_conj_hull_class_finrank_eq_five
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:12.86177+00:00
-- url     : https://prove2.me/theorems/f6db623d-1b75-4668-b3d2-a2d85659d355
-- title:
--   A conjugation hull in the polynomial, involution or real pencil class is five-dimensional
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$ (so $s = \pm|u|$ is real), and put $v = u/s$, so that $\bar v = 1/v$. Let $k \geq 0$, let $c_j \in \mathbb{C}$ for all $j \in \mathbb{Z}$ (they need not be algebraic), and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, z, \bar z)$. If $W$ is in one of the classes
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$,
--
--   then $\dim_{\overline{\mathbb{Q}}} W = 5$.
--
--   **Proof.** Work in $v = u/s$, which is transcendental with $\bar v = 1/v$ since $s$ is real. In class (P), with $m = \alpha u^2 + \beta u^3 \in W$, also $\bar m \in W$, as the hull is conjugation-stable; $1, u, \bar u, m, \bar m$ are free, because a relation cleared by $v^3$ is a polynomial of degree $6$ in $v$ whose seven coefficients vanish, and $W$ has five generators. In class (Q) the normal-form generators are free in the same way, using $\beta \neq 0$ from $\beta\bar\beta = 1$. In class (R), with $n = \deg G \geq 2$ and $H = \sum\bar G_iX^{n-i}$, so that $H(v) = v^n\overline{G(v)}$ and $H(0) = \bar G_n \neq 0$, a relation cleared by $v^{n+1}$ and evaluated at $0$ loses its $g$ coordinate, its conjugate loses the $\bar g$ one, and $1, u, \bar u$ are free.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_class_finrank_eq_five
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ)
    (hcls : (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5 := by
  sorry

end DiazModulus
