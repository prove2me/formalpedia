-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_theorem_1_1
-- name    : DiscIsoCurvature.Cube.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:08:17.095842+00:00
-- url     : https://prove2.me/theorems/9126d188-4930-45c2-a642-f2a7762b57e9
-- title:
--   Theorem 1.1 — KKL, Talagrand's L1–L2 and variance–surface-area, and Eldan–Gross inequalities under marginal boundedness and the Dobrushin condition, one constant C(b, δ, C₀)
-- statement:
--   Let $b\in(0,1]$, $\delta\in(0,1)$ and $C_0>0$. There is a constant $C>0$, depending only on $b,\delta,C_0$, such that the following holds for every $n\ge1$. Let $\mu$ be a fully supported distribution on $\{\pm1\}^n$ with
--
--   (i) (marginal boundedness) $b\le\sqrt{\mu(x^i)/\mu(x)}\le1/b$ for every $i\in[n]$ and $x$;
--
--   (ii) (Dobrushin condition) the Dobrushin matrix $R$ of $\mu$ (Eq. (6)) satisfies $\|R\|_1\le C_0$ (maximum column sum) and $\|R\|_2\le1-\delta$ (spectral norm).
--
--   Then every Boolean $f:\{\pm1\}^n\to\{\pm1\}$ satisfies all four of
--   $$\max_{i}\mathrm{Inf}_{\mu,i}(f)\ge C\frac{\log n}{n}\mathrm{Var}_\mu(f),\qquad C\,\mathrm{Var}_\mu(f)\le\sum_{i=1}^n\frac{\mathrm{Inf}_{\mu,i}(f)}{1+\log(1/\mathrm{Inf}_{\mu,i}(f))},$$
--   $$\mathrm{SA}_\mu(f)\ge C\,\mathrm{Var}_\mu(f)\sqrt{\log\frac e{\mathrm{Var}_\mu(f)}},\qquad \mathrm{SA}_\mu(f)\ge C\,\mathrm{Var}_\mu(f)\sqrt{\log\Big(1+\frac e{\mathrm{SqInf}_\mu(f)}\Big)},$$
--   the KKL (7), Talagrand L1–L2 (8), variance–surface-area (9) and Eldan–Gross (10) inequalities, where influences, surface area and squared influence are taken under $\mu$ (§1.1). It extends the four classical uniform-measure inequalities to weakly dependent, non-product measures.
--
--   Differences from the source:
--
--   - encoding: Ω = {±1}^n, x^i, [n] → BoolCube n = Fin n → Bool (true ↔ +1), x^i = flip x i, coordinates in Fin n; reason: a bijective relabelling of the cube and of the index set [n]
--   - reading: C > 0 depends only on b, δ and C0, but not on n → one ∃ C > 0 after b, δ, C₀ and before n, µ, f, shared by (7)–(10); reason: the stronger reading: one constant for all four inequalities and all n
--   - encoding: n (implicitly n ≥ 1: max over i ∈ [n]) → hypothesis 1 ≤ n; reason: the maximum in (7) is over a nonempty index set only for n ≥ 1
--   - encoding: a summand of (8) is zero when Inf_{µ,i}(f) = 0 (p. 2, by continuity) → if Inf_{µ,i}(f) = 0 then 0 else …; reason: the paper's convention for (3), which (8) restates, written out
--   - encoding: the right side of (9) when Var_µ(f) = 0 (f constant) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
--   - encoding: e/SqInf_µ(f) in (10) when SqInf_µ(f) = 0 (then f is constant and Var_µ(f) = 0) → Lean's x/0 = 0 and log 0 = 0; reason: both sides are 0 in that degenerate case, which is the paper's value
--   - encoding: max_{i∈[n]} Inf_{µ,i}(f) → ⨆ i : Fin n, Inf_{µ,i}(f); reason: a maximum over the finite nonempty set Fin n (n ≥ 1)
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic
import Definitions.Def_DiscIsoCurvature_Cube_Influence
import Definitions.Def_DiscIsoCurvature_Cube_Dobrushin

namespace DiscIsoCurvature.Cube

/-- Theorem 1.1 (p. 4): for constants `b ∈ (0, 1]`, `δ ∈ (0, 1)`, `C₀ > 0` there is `C > 0`
(depending only on `b, δ, C₀`) such that for every `n ≥ 1`, every fully supported distribution
`μ` on `{±1}^n` with (i) `b ≤ √(μ(x^i)/μ(x)) ≤ 1/b` for all `i, x` and (ii) Dobrushin matrix
`R` (Eq. (6)) with `‖R‖₁ ≤ C₀`, `‖R‖₂ ≤ 1 − δ`, and every Boolean `f`, all of
(7) `maxᵢ Inf_{μ,i}(f) ≥ C (log n/n) Var_μ(f)`,
(8) `C Var_μ(f) ≤ ∑ᵢ Inf_{μ,i}(f)/(1 + log(1/Inf_{μ,i}(f)))` (a summand is `0` when
`Inf_{μ,i}(f) = 0`),
(9) `SA_μ(f) ≥ C Var_μ(f) √(log(e/Var_μ(f)))`,
(10) `SA_μ(f) ≥ C Var_μ(f) √(log(1 + e/SqInf_μ(f)))` hold. -/
theorem theorem_1_1 (b δ C₀ : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ μ : BoolCube n → ℝ, IsFullDist μ →
        (∀ i x, b ≤ Real.sqrt (μ (flip x i) / μ x) ∧ Real.sqrt (μ (flip x i) / μ x) ≤ 1 / b) →
        colSumNorm (dobrushinCube μ) ≤ C₀ → specNorm (dobrushinCube μ) ≤ 1 - δ →
        ∀ f : BoolCube n → ℝ, IsBoolean f →
          C * (Real.log n / n) * var μ f ≤ (⨆ i, influence μ f i) ∧
          C * var μ f ≤
            ∑ i, (if influence μ f i = 0 then 0 else
              influence μ f i / (1 + Real.log (1 / influence μ f i))) ∧
          C * var μ f * Real.sqrt (Real.log (Real.exp 1 / var μ f)) ≤ surfaceArea μ f ∧
          C * var μ f * Real.sqrt (Real.log (1 + Real.exp 1 / sqInfluence μ f))
            ≤ surfaceArea μ f := by sorry

end DiscIsoCurvature.Cube
