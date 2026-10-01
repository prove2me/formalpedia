-- Prove2me | Theorems.Thm_DiazModulus_pi_powers_not_both_mem_logAlgTilde
-- name    : DiazModulus.pi_powers_not_both_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:52:13.034987+00:00
-- url     : https://prove2.me/theorems/f866520f-d5c9-472d-b572-2c4caeca5231
-- title:
--   Under the strong six exponentials theorem, π² and π³, π² and 1/π, 1/π and 1/π² are pairwise not both in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   1. $\pi^2$ and $\pi^3$ are not both in $\widetilde{\mathcal{L}}$.
--   2. $\pi^2$ and $1/\pi$ are not both in $\widetilde{\mathcal{L}}$.
--   3. $1/\pi$ and $1/\pi^2$ are not both in $\widetilde{\mathcal{L}}$.
--   4. If $e^{\gamma/(\pi i)}$ is algebraic for some algebraic $\gamma \neq 0$, then $e^{\beta\pi^2}$ and $e^{\beta/\pi^2}$ are transcendental for every algebraic $\beta \neq 0$.
--
--   Part 4 concerns the statement (S) of the Diaz mission, that $e^{\gamma/(\pi i)}$ is transcendental for every algebraic $\gamma \neq 0$ (`DiazModulus.recip_pi_not_log`, Open). Under the strong six exponentials theorem, an exception to (S) would make $e^{\pi^2}$ transcendental. Part 1 is the $\widetilde{\mathcal{L}}$ strengthening of the unconditional `DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental`.
--
--   **Proof.** Parts 1–3 are Conséquence 3 of Corollaire 2 (P) and the two "in particular" clauses of Corollaire 1 (PQ) 3) and 4) at $\lambda = i\pi$ (`DiazModulus.diaz_2007_cor2_P_consequences`, `DiazModulus.diaz_2007_cor1_PQ`). Here $i\pi \in \mathcal{L}$ and is transcendental by Hermite–Lindemann. For part 4, $\gamma/(\pi i) \in \mathcal{L}$ gives $1/\pi \in \widetilde{\mathcal{L}}$, and parts 2 and 3 exclude $\pi^2$ and $1/\pi^2$.
--
--   **Novelty.** None: Diaz (2007) draws parts 1–3 himself at $\lambda = i\pi$, as statements on $\exp(\pi^2)$, $\exp(\pi^3)$, $\exp(1/\pi)$ and $\exp(1/\pi^2)$ (pp. 380–381). Part 4 restates parts 2 and 3. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, the remarks at λ = iπ after Corollaire 1 (PQ) (p. 380) and after Conséquence 3 of Corollaire 2 (P) (p. 381). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- Under Roy's strong six exponentials theorem, `π²` and `π³`, `π²` and `1/π`, `1/π` and `1/π²` are pairwise
not both in `ℒ̃`; and if `e^{γ/(πi)}` is algebraic for some algebraic `γ ≠ 0`, then `e^{βπ²}` and `e^{β/π²}` are
transcendental for every algebraic `β ≠ 0`. -/
theorem pi_powers_not_both_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    ¬ (((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde ∧ ((Real.pi : ℝ) : ℂ) ^ 3 ∈ LogAlgTilde) ∧
    ¬ (((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde ∧ 1 / ((Real.pi : ℝ) : ℂ) ∈ LogAlgTilde) ∧
    ¬ (1 / ((Real.pi : ℝ) : ℂ) ∈ LogAlgTilde ∧ 1 / ((Real.pi : ℝ) : ℂ) ^ 2 ∈ LogAlgTilde) ∧
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∀ β : ℂ, IsAlgebraic ℚ β → β ≠ 0 →
        Transcendental ℚ (Complex.exp (β * ((Real.pi : ℝ) : ℂ) ^ 2)) ∧
        Transcendental ℚ (Complex.exp (β / ((Real.pi : ℝ) : ℂ) ^ 2))) := by
  sorry

end DiazModulus
