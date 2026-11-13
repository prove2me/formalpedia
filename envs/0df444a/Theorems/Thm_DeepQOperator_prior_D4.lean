-- Prove2me | Theorems.Thm_DeepQOperator_prior_D4
-- name    : DeepQOperator.prior_D4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:45.989871+00:00
-- url     : https://prove2.me/theorems/00550893-9f72-4195-98a7-8cbfc6fbfe03
-- title:
--   D.4 and (40): the common hard prior and its boundary matrix $\mathrm{diag}(0,\frac{\gamma}{256\pi^2m}I_m)$
-- statement:
--   Let $m\ge2$, $0<\gamma<1$. Take independent cosine-squared coordinates with address radius $1/8$ and payload radius $1/4$, centers $x_i=(3c_i/4,\frac12\mathbf 1_m)$, and the swept points $\theta=x_i+X-Te_{z_i}$ with $X$ in the support and $T\in[-1/4,1/4]$. Then:
--   1. the support of the prior is the box $[-1/8,1/8]^n\times[-1/4,1/4]^m$;
--   2. every swept point lies in $P_{cb}$; there $b_i\ge5/16>1/4$, $b_j\le1/16$ for $j\ne i$, every other payload feature satisfies $b_j+z_j/16\le1/8$, and the selected feature wins both maxima: $A=b_i+z_i/16$, $B=b_i$;
--   3. $g(x_i+X-Te_{z_i})=\frac{\gamma}{16}(X_{z_i}-T)$;
--   4. the score matrix is finite and equals $\pi^2\,\mathrm{diag}(64I_n,16I_m)$;
--   5. with $p_i=1/m$, $n_i=v_i=e_{z_i}$, $R_i=1/4$ and contrast multiplier $\gamma/16$, the boundary matrix is
--   $$B=\mathrm{diag}\Big(0_{n\times n},\ \frac{\gamma}{256\pi^2m}I_m\Big).\tag{40}$$
--
--   These are the hypotheses of Theorem 6 for the family (6), with $m$ equal eigenvalues $\gamma/(256\pi^2m)$.
--
--   **Formalization Note** $X$ ranges over the closed support, written coordinatewise, and $e_{z_i}$ is the indicator of payload coordinate $i$. $I^{-1/2}$ is any positive definite $S$ with $S^2=I^{-1}$.
--
--   Differences from the source:
--   - generalization: "The payload Fisher diagonal is 16π² and the address diagonal is 64π²" → the score matrix is finite and equal to diag(64π² on addresses, 16π² on payloads); reason: off-diagonal entries vanish by independence and (93); (40) and Theorem 6 need them
--   - encoding: "the selected feature uniquely wins both maxima" → A = b_i + z_i/16, B = b_i, and every other feature ≤ 1/8 < b_i; reason: uniqueness follows from the strict gap
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix D.4, eq. (40), p.22 (PDF p.25)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_ScoreMatrix

open MeasureTheory Matrix

namespace DeepQOperator

/-- **The common continuous hard prior of Appendix D.4 and (40)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix D.4, p.22,
PDF p.25).

Take independent cosine-squared coordinates with address radius `1/8` and payload radius `1/4`,
centers `x_i = (3c_i/4, (1/2)1_m)`, and swept points `θ = x_i + X - T e_{z_i}` with `X` in the support
and `T ∈ [-1/4, 1/4]`. Then:
1. the support of the prior is the box `[-1/8,1/8]^n × [-1/4,1/4]^m`;
2. every swept point lies in `P_cb`, and there `b_i ≥ 5/16` and `b_j ≤ 1/16` for `j ≠ i`; the selected
   baseline is strictly above `1/4`, every other payload feature is at most `1/16 + 1/16 = 1/8`, and the
   selected feature wins both maxima (`A = b_i + z_i/16`, `B = b_i`);
3. `g(x_i + X - T e_{z_i}) = (γ/16)(X_{z_i} - T)`;
4. the score matrix is finite, with address diagonal `64π²` and payload diagonal `16π²`;
5. (40): with `p_i = 1/m`, `n_i = v_i = e_{z_i}`, `R_i = 1/4` and contrast multiplier `γ/16`, the
   boundary matrix is `B = diag(0_{n×n}, (γ/(256π²m)) I_m)`.

**Formalization Note.** `X` is a point `y` of `tsupport ρ` for the product density `ρ`, written
coordinatewise as the closed box, and `θ` names the swept point `x_i + y - t e_{z_i}`; `e_{z_i}` is the indicator of the coordinate `Sum.inr i`. In (40),
`I^{-1/2}` is any positive definite `S` with `S * S = I⁻¹` (unique).
-/
theorem prior_D4 (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    tsupport (productDensity (Sum.elim (fun _ : Addr m => (1 / 8 : ℝ)) (fun _ : Fin m => 1 / 4))) =
      {y | (∀ v, |y (Sum.inl v)| ≤ 1 / 8) ∧ ∀ j, |y (Sum.inr j)| ≤ 1 / 4} ∧
    (∀ (i : Fin m) (y : Coord m → ℝ) (t : ℝ) (θ : Coord m → ℝ),
      (∀ v, |y (Sum.inl v)| ≤ 1 / 8) → (∀ j, |y (Sum.inr j)| ≤ 1 / 4) →
      t ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4) →
      θ = Sum.elim (fun v => 3 / 4 * walsh (rr m) i v) (fun _ => 1 / 2) + y -
          t • (fun c : Coord m => if c = Sum.inr i then (1 : ℝ) else 0) →
      θ ∈ Pcb m ∧ 5 / 16 ≤ bScore m i θ ∧ (∀ j ≠ i, bScore m j θ ≤ 1 / 16) ∧
      1 / 4 < bScore m i θ ∧ (∀ j ≠ i, bScore m j θ + θ (Sum.inr j) / 16 ≤ 1 / 8) ∧
      rowA m θ = bScore m i θ + θ (Sum.inr i) / 16 ∧ rowB m θ = bScore m i θ ∧
      contrast m γ θ = γ / 16 * (y (Sum.inr i) - t)) ∧
    FiniteFisher (productDensity (Sum.elim (fun _ : Addr m => (1 / 8 : ℝ)) (fun _ : Fin m => 1 / 4))) ∧
    fisherMatrix (productDensity (Sum.elim (fun _ : Addr m => (1 / 8 : ℝ)) (fun _ : Fin m => 1 / 4))) =
      Matrix.diagonal (Sum.elim (fun _ => 64 * Real.pi ^ 2) (fun _ => 16 * Real.pi ^ 2)) ∧
    (∀ S : Matrix (Coord m) (Coord m) ℝ, S.PosDef →
      S * S = (fisherMatrix
        (productDensity (Sum.elim (fun _ : Addr m => (1 / 8 : ℝ)) (fun _ : Fin m => 1 / 4))))⁻¹ →
      boundaryMatrix S (fun _ : Fin m => 1 / (m : ℝ)) (fun _ => γ / 16) (fun _ => 1 / 4)
          (fun i c => if c = Sum.inr i then 1 else 0) =
        Matrix.diagonal (Sum.elim (fun _ => 0) (fun _ => γ / (256 * Real.pi ^ 2 * m)))) := by sorry

end DeepQOperator
