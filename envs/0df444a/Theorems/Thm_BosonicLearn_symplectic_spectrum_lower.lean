-- Prove2me | Theorems.Thm_BosonicLearn_symplectic_spectrum_lower
-- name    : BosonicLearn.symplectic_spectrum_lower
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:00:16.781212+00:00
-- url     : https://prove2.me/theorems/c34bc7c4-ffec-4fe6-a216-3cd6f9eb4d92
-- title:
--   $\Sigma\succeq c\,I$ implies every eigenvalue $z$ of $\Omega\Sigma$ has $|z|\ge c$ (symplectic eigenvalues $\ge c$)
-- statement:
--   Ordinary-to-symplectic eigenvalue comparison.
--
--   Let $S$ be a real symmetric $2n\times2n$ matrix with $S\succeq c\,\mathbf 1$ for some $c\ge0$, and $\Omega=\begin{pmatrix}0&\mathbf 1_n\\-\mathbf 1_n&0\end{pmatrix}$. Then every complex eigenvalue $z$ of $\Omega S$ satisfies $|z|\ge c$.
--
--   For a covariance matrix $\Sigma$ the spectrum of $\Omega\Sigma$ is $\{\pm\mathrm i\nu_j\}$ with $\nu_j$ the symplectic eigenvalues, so $\Sigma\succeq(\tfrac12+\nu)\mathbf 1$ implies that all symplectic eigenvalues are at least $\tfrac12+\nu$.
--
--   Role. This verifies the hypothesis of Theorem 7 (symplectic eigenvalues of $\bar\Sigma$ at least $\nu_->\tfrac12$) for states of the promise class in the proof of Theorem 8.
--
--   **Formalization Note** The conclusion has the form of the hypothesis `hsympl` of `BosonicLearn.theorem_7`: for every `z ∈ spectrum ℂ ((Ω * S).map (↑))`, `c ≤ ‖z‖`, with `Ω = Matrix.fromBlocks 0 1 (-1) 0` in the grouped quadrature order. The hypothesis is `Matrix.PosSemidef (S − c • 1)`. Pure linear algebra.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, p. 62 ("the ordinary-to-symplectic eigenvalue comparison", proof of Theorem 8); Theorem 7, p. 55

import Mathlib

open scoped Matrix

namespace BosonicLearn

/-- **Ordinary-to-symplectic eigenvalue comparison.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, p. 62: "The same promise also implies that every symplectic eigenvalue of Σ is at
least 1/2 + ν, by the ordinary-to-symplectic eigenvalue comparison proved above."

Let `S` be a real symmetric `2n × 2n` matrix with `S ⪰ c I`, `c ≥ 0`, and `Ω = [[0, I], [−I, 0]]`. Then every
complex eigenvalue `z` of `ΩS` satisfies `|z| ≥ c`. For a covariance matrix the spectrum of `ΩΣ` is
`{± i ν_j}` with `ν_j` the symplectic eigenvalues, so all symplectic eigenvalues are at least `c`.

**Formalization Note.** This is the hypothesis `hsympl` of `theorem_7` (with `νm = c`), in the same form:
`z ∈ spectrum ℂ ((Ω * S).map (↑))`. -/
theorem symplectic_spectrum_lower {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hS : (S - c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef) :
    ∀ z ∈ spectrum ℂ ((Matrix.fromBlocks 0 1 (-1) 0 * S).map (fun x : ℝ => (x : ℂ))),
      c ≤ ‖z‖ := by sorry

end BosonicLearn
