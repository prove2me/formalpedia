-- Prove2me | Theorems.Thm_DiazModulus_power_hull_strong_six_exp_configuration_iff
-- name    : DiazModulus.power_hull_strong_six_exp_configuration_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:32:29.288833+00:00
-- url     : https://prove2.me/theorems/e31ad15c-0c6d-4572-b443-953da5c153e1
-- title:
--   Strong six exponentials configurations in the span of u^{±k}, u^{±1}, 1 exist exactly for k = 2 and k = 3
-- statement:
--   Let $u$ be transcendental and $k \geq 1$. There exist $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_iy_j$ in
--
--   $$\overline{\mathbb{Q}}\,u^{-k} + \overline{\mathbb{Q}}\,u^{-1} + \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,u + \overline{\mathbb{Q}}\,u^{k}$$
--
--   if and only if $k = 2$ or $k = 3$.
--
--   **Why it matters for Diaz's conjecture.** At a candidate $u$ ($|u|$ and $e^u$ algebraic) the space $\widetilde{\mathcal{L}}$ contains $1$, $u$ and $\bar u = |u|^2/u$, and if it contained $u^k$ it would contain $\bar u^k = |u|^{2k}u^{-k}$ too. Roy's strong six exponentials theorem refutes $u^k \in \widetilde{\mathcal{L}}$ through numbers built from $u$ alone exactly when a configuration as above exists. So it excludes $u^2$ (`DiazModulus.candidate_multiplier_module`) and $u^3$ (`DiazModulus.candidate_cube_and_axis_multiple_not_mem_logAlgTilde`), and by this route nothing further: not $u^4$, nor any higher power. Configurations that also use logarithms unrelated to $u$ are not covered.
--
--   **Proof.** For $k = 2$ take $x = (1, u)$, $y = (u^{-1}, 1, u)$; for $k = 3$ take $x = (u, u^{-1})$, $y = (1, u^{-2}, u^2)$ (Diaz's configuration for his Corollaire 5(2), up to the factor $|u|^2$). For $k = 1$ and $k \geq 4$, multiply by $u^k$: since $u$ is transcendental, the products become polynomials supported on $E = \{0, k-1, k, k+1, 2k\}$, and the rank-one relations become polynomial identities. The orders at $0$ of the three independent polynomials of the first row are three distinct exponents $t$ with $t$ and $t + \delta$ both in $E$, for a fixed $\delta \neq 0$. But for $k = 1$ and for $k \geq 4$ at most two such $t$ exist for every $\delta \neq 0$.
--
--   **Novelty.** Not found in the sources read (Diaz 1997, 2004, 2007; Waldschmidt's *Variations*, *Further variations* and *The role of complex conjugation*; Roy–Waldschmidt 1995, and 1997 §§0 and 7; *Diophantine Approximation on Linear Algebraic Groups*, §§11.5–11.6 and chapter 12). Diaz notes that his list of conjectures contains no general one for $\lambda^n$ (2007, p. 376), and that inside the strong six exponentials theorem one cannot hope to go very far (p. 390); this node is a precise instance of the second remark.
-- source:
--   Context: G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, p. 376, Corollaire 5 (p. 383), Théorème 7 and §2.4 (p. 390). Not found in the sources read. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- For transcendental `u` and `k ≥ 1`, a configuration of the strong six exponentials theorem (two
`Q̄`-independent `xᵢ`, three `Q̄`-independent `yⱼ`) with all six products in
`Q̄ u⁻ᵏ + Q̄ u⁻¹ + Q̄ + Q̄ u + Q̄ uᵏ` exists exactly when `k = 2` or `k = 3`. -/
theorem power_hull_strong_six_exp_configuration_iff {u : ℂ} (hu : u ∉ Qbar) {k : ℕ} (hk : 1 ≤ k) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({(u ^ k)⁻¹, u⁻¹, 1, u, u ^ k} : Set ℂ)) ↔
    (k = 2 ∨ k = 3) := by
  sorry

end DiazModulus
