-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_6
-- name    : DistRobustHalfspace.Main.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:25.102647+00:00
-- url     : https://prove2.me/theorems/75f0deed-7162-4ab9-931b-d4998006aafe
-- title:
--   Lemma 2.6 — normal vector estimator in the YES case: E[ṽ(t̂)] = (1 + a)v
-- statement:
--   Let $f(x)=\operatorname{sign}(\langle x,v\rangle-t)$ with $v$ a unit vector and $t\in\mathbb R$. Let $\xi\ge0$ and let $\hat t$ be a $\xi$-good threshold estimate for $f$, i.e. $|t-\hat t|\le\xi$. Then
--   $$\mathbb E[\tilde v(\hat t)]=(1+a)\,v\quad\text{for some }a\in\mathbb R\text{ with }|a|\le\sqrt{2/\pi}\cdot\frac{\xi(|\hat t|+\xi)}{\tau(\hat t)},$$
--   where $\mathbb E[\tilde v(\hat t)]=\mathbb E_{x\sim\mathcal N(0,I_n)}[x f(x)]/\tau(\hat t)$.
--
--   Differences from the source:
--   - generalization: standing assumption n ≥ n₀ of §§2–3 → every dimension n; reason: the statement is dimension-free; it specializes to n ≥ n₀
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: ℝⁿ → `Rn n = EuclideanSpace ℝ (Fin n)`; reason: Lean's Euclidean ℝⁿ with its Borel σ-algebra
--   - encoding: E[ṽ(t̂)] (Definition 2.3) → `meanNormalEst f t̂ = (τ t̂)⁻¹ • ∫ f(x) • x dN(0, Iₙ)`; reason: the mean of x f(x)/τ(t̂) for x ∼ N(0, Iₙ)
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.6, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.6 (p. 13): for the halfspace `f(x) = sign(⟨x, v⟩ − t)` with unit `v` and a `ξ`-good
threshold estimate `t̂`, `E[ṽ(t̂)] = (1 + a) v` with `|a| ≤ √(2/π) · ξ(|t̂| + ξ) / τ(t̂)`. -/
theorem lemma_2_6 {n : ℕ} (v : Rn n) (t : ℝ) (hv : ‖v‖ = 1) (f : Rn n → ℝ)
    (hf : ∀ x, f x = sgn (⟪x, v⟫ - t)) (ξ t' : ℝ) (hξ : 0 ≤ ξ) (hgood : |t - t'| ≤ ξ) :
    ∃ a : ℝ, meanNormalEst f t' = (1 + a) • v ∧
      |a| ≤ Real.sqrt (2 / Real.pi) * (ξ * (|t'| + ξ)) / tau t' := by sorry

end DistRobustHalfspace.Main
