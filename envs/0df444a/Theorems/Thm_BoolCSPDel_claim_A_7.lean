-- Prove2me | Theorems.Thm_BoolCSPDel_claim_A_7
-- name    : BoolCSPDel.claim_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:48.958207+00:00
-- url     : https://prove2.me/theorems/4cdf3540-d212-4ecb-94b7-2ee2916933c2
-- title:
--   Claim A.7 — the row test
-- statement:
--   Let $H$ be as in Lemma A.3, $b_i$ a nonzero row, $v_i$ the output of Algorithm 7, $q_i=b_i^\top v_i$ and $q^*_i=b_i^\top H^{-1}b_i$. Then $q_i>0$ and
--
--   $$0.96q^*_i\le\frac{q_i^2}{v_i^\top Hv_i}\le q^*_i.$$
--
--   Fix $z\ge0$, put $y=\mathrm{diag}(z)Bv_i$, $M_z=\ell I+\sum_iz_i^2b_ib_i^\top$ and $R_i=(z_iq_i)^2/(v_i^\top M_zv_i)$, and suppose estimates $\hat y_i,\hat\nu_i$ satisfy (A.2). At threshold $\vartheta\in\{\eta,\theta\}$, every row with $R_i\ge4\vartheta$ passes the acceptance tests, and every row passing them has $R_i\ge\vartheta$ and $z_i>0$. If a passing row has $z_i\ge0.99$, its rounded estimate satisfies $|\hat z_i-z_i|\le\varepsilon_az_i$ and is positive.
--
--   This is what makes the test detect exactly the rows with large contribution.
--
--   Differences from the source:
--   - reading: "If z_i ≥ 0.99, its rounded estimate satisfies" → for a row passing the acceptance tests; reason: Claim A.14, p.58, says "For a row passing them with z_i ≥ 0.99"; a rejected row has no estimate
--   - encoding: round_g with "fixed tie breaking" → g · round(x / g), ties rounded up; reason: one fixed tie-breaking rule, as the page allows any
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Claim A.7, p.57; pp.56–57

import Mathlib
import Definitions.Def_BoolCSPDel_decode
import Definitions.Def_BoolCSPDel_dictOracle

namespace BoolCSPDel

/-- **Claim A.7 (the row test).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Claim A.7, p.57, with the objects of pp.56–57.

For `H` as in Lemma A.3, a nonzero row `b_i`, `v_i` from Algorithm 7, `q_i = b_iᵀv_i` and `q*_i = b_iᵀH⁻¹b_i`:
`q_i > 0` and `0.96 q*_i ≤ q_i²/(v_iᵀHv_i) ≤ q*_i`. Fix `z ≥ 0`, put `y = diag(z)Bv_i`, `M_z = ℓI + Σ z_i²b_ib_iᵀ`,
`R_i = (z_iq_i)²/(v_iᵀM_zv_i)`, and let estimates `ŷ_i`, `ν̂_i` satisfy (A.2). At `ϑ ∈ {η, θ}`, every row with
`R_i ≥ 4ϑ` passes the acceptance tests (`ŷ_i > 0`, `ŷ_i² ≥ 2ϑ(ν̂_i + ℓ‖v_i‖²)`), every row passing has `R_i ≥ ϑ` and
`z_i > 0`, and a passing row with `z_i ≥ 0.99` has `|ẑ_i − z_i| ≤ ε_a z_i`, `ẑ_i > 0`, for `ẑ_i = round_{g_a}(ŷ_i/q_i)`.

**Formalization Note.** The rounded estimate is about a passing row (Claim A.14, p.58, "For a row passing them
with `z_i ≥ 0.99`"). `H⁻¹` is the nonsingular inverse, and `H` is positive definite here. -/
theorem claim_A_7 (P : Params) (hm : 1 ≤ P.m) (hD : 1 ≤ P.D) (hμ : 1 ≤ P.μ) (he : 3 ≤ P.e)
    (hg : 2 ≤ P.g) (s₀ : ℕ) (B : Matrix (Fin P.m) (Fin P.D) ℤ) (hB : SparseRows s₀ P.b₀ B)
    (j : ℕ) (hj : j < P.K) (l : List (Fin P.m × ℚ)) (hl : ValidRep P l) (i : Fin P.m)
    (hi : rowQ B i ≠ 0) :
    let ell : ℝ := (P.lamJ j : ℝ)
    let H := hMatrix B ell l
    let vq := computeV P B (P.lamJ j) (l.map fun e => (e.1, e.2 ^ 2)) i
    let v : Fin P.D → ℝ := fun c => (vq c : ℝ)
    let q : ℝ := rowR B i ⬝ᵥ v
    let qStar : ℝ := rowR B i ⬝ᵥ (H⁻¹.mulVec (rowR B i))
    (0 < q ∧ (24 / 25 : ℝ) * qStar ≤ q ^ 2 / (v ⬝ᵥ H.mulVec v) ∧ q ^ 2 / (v ⬝ᵥ H.mulVec v) ≤ qStar) ∧
    ∀ (z : Fin P.m → ℝ), (∀ a, 0 ≤ z a) →
      let y : Fin P.m → ℝ := fun a => z a * (rowR B a ⬝ᵥ v)
      let Mz : Matrix (Fin P.D) (Fin P.D) ℝ := ell • (1 : Matrix _ _ ℝ) +
        ∑ a, (z a) ^ 2 • Matrix.vecMulVec (rowR B a) (rowR B a)
      let R : ℝ := (z i * q) ^ 2 / (v ⬝ᵥ Mz.mulVec v)
      ∀ (vartheta yh nu : ℝ), (vartheta = (P.eta : ℝ) ∨ vartheta = (P.theta : ℝ)) →
        EstimatesOK ((P.epsA : ℝ) * Real.sqrt (P.eta : ℝ) / 100) y i yh nu →
        let accept : Prop := 0 < yh ∧ 2 * vartheta * (nu + ell * (v ⬝ᵥ v)) ≤ yh ^ 2
        (4 * vartheta ≤ R → accept) ∧
        (accept → vartheta ≤ R ∧ 0 < z i) ∧
        (accept → (99 / 100 : ℝ) ≤ z i →
          let zh : ℝ := (P.ga : ℝ) * (round (yh / q / (P.ga : ℝ)) : ℝ)
          |zh - z i| ≤ (P.epsA : ℝ) * z i ∧ 0 < zh) := by sorry

end BoolCSPDel
