-- Prove2me | Theorems.Thm_DiazModulus_config_shifted_polynomial_spans
-- name    : DiazModulus.config_shifted_polynomial_spans
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:58:48.959231+00:00
-- url     : https://prove2.me/theorems/b54c411d-622a-4c97-8c55-51676e45fce0
-- title:
--   A 2×3 configuration whose products, times u^N, are values at u of polynomials in H gives polynomial spans with f·g ∈ P₀·H
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, $H \subseteq \overline{\mathbb{Q}}[X]$ a subspace, $N \geq 0$, and let free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ satisfy $u^Nx_iy_j = Q_{ij}(u)$ with $Q_{ij} \in H$. Then there are free $a_1, a_2$, free $b_1, b_2, b_3$ and $P_0 \neq 0$ in $\overline{\mathbb{Q}}[X]$ such that for every $f$ in the span of the $a_i$ and every $g$ in the span of the $b_j$, $fg = P_0h$ for some $h \in H$.
--
--   **Proof.** Take $a_i = Q_{i0}$, $b_j = Q_{0j}$ and $P_0 = Q_{00}$. As $u$ is transcendental, evaluation at $u$ is injective on $\overline{\mathbb{Q}}[X]$. $P_0 \neq 0$ because $P_0(u) = u^Nx_0y_0 \neq 0$; $a_i(u) = (u^Ny_0)x_i$ and $b_j(u) = (u^Nx_0)y_j$, so $a$ and $b$ are free. For $f = \sum c_ia_i$ and $g = \sum d_jb_j$ put $h = \sum c_id_jQ_{ij}$: at $u$ both $fg$ and $P_0h$ equal $u^{2N}x_0y_0(\sum c_ix_i)(\sum d_jy_j)$, so $fg = P_0h$.
--
--   **Novelty.** Not found in the sources read in this form; it is the normalisation in the proof of `DiazModulus.laurent_hull_config_iff`, for any polynomial hull. Routine.
-- source:
--   Not found in the sources read in this form; the normalisation in the proof of DiazModulus.laurent_hull_config_iff. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem config_shifted_polynomial_spans {u : ℂ} (hu : u ∉ Qbar)
    (Hull : Submodule (↥Qbar) (↥Qbar)[X]) (N : ℕ)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, ∃ Q ∈ Hull, aeval u Q = u ^ N * (x i * y j)) :
    ∃ (a : Fin 2 → (↥Qbar)[X]) (b : Fin 3 → (↥Qbar)[X]) (P₀ : (↥Qbar)[X]),
      LinearIndependent (↥Qbar) a ∧ LinearIndependent (↥Qbar) b ∧ P₀ ≠ 0 ∧
      ∀ f ∈ Submodule.span (↥Qbar) (Set.range a), ∀ g ∈ Submodule.span (↥Qbar) (Set.range b),
        ∃ h ∈ Hull, f * g = P₀ * h := by
  sorry

end DiazModulus
