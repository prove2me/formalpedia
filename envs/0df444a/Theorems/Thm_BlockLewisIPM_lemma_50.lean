-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_50
-- name    : BlockLewisIPM.lemma_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:22.456978+00:00
-- url     : https://prove2.me/theorems/9d741721-ed66-4679-beed-2786fe1f4587
-- title:
--   Lemma 50 — exact feasibility and the final gap
-- statement:
--   Let $(x,s,\rho)$ be $\epsilon$-centered for the program, with $A$ of full column rank, and let $\bar\tau$ satisfy $\|T(x)^{-1}(\tau(x)-\bar\tau)\|_\infty\le\alpha$. Define
--
--   $$x^{(\mathrm{fi})}=x-\bar T^{-1}\nabla^2\Phi(x)^{-1}A\bigl(A^\top\bar T^{-1}\nabla^2\Phi(x)^{-1}A\bigr)^{-1}(A^\top x-b),\qquad s^{(\mathrm{fi})}=s .$$
--
--   Then $x^{(\mathrm{fi})}$ is primal feasible, $s^{(\mathrm{fi})}$ is dual feasible, and
--
--   $$c^\top x^{(\mathrm{fi})}-\min_{x\in K,\,A^\top x=b}c^\top x\le8\rho d .$$
--
--   This turns an approximately feasible centered point into an exactly feasible near-optimal one.
--
--   Differences from the source:
--   - reading: "we can compute a feasible pair" → the pair defined in the proof, p.90; reason: the stronger reading
--   - reading: T̄ in x^(fi) (p.90) with τ̄ undefined in the lemma → any α-approximation τ̄ of τ(x), including τ̄ = τ(x); reason: covers both the T̄ and the T printed on p.90
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
--   - reading: min over the feasible set → ∀ feasible y, c⊤x^(fi) ≤ 8ρd + c⊤y; reason: no junk value of sInf; equal when the min exists
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 50, p.45, and its proof, pp.90–91

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 50**, p.45, with the pair of its proof, p.90. Zhang, Wright, *A Fast Lewis-weight Interior Point
Method for Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** "We can compute a feasible pair" is the pair the proof defines, `x^(fi)` and
`s^(fi) = s`, the stronger reading. The page prints `T̄` in `x^(fi)` and `T` in the bound below it; here `τ̄` is
any `α`-approximation of `τ(x)`, which includes `τ̄ = τ(x)`. `A` has full column rank (reading R10). `min`
is read as `∀` feasible `y` (reading R7). `ϵ` ranges over Definition 17's `(0, 1/100]`. -/
theorem lemma_50 : ∃ C₀ : ℝ, 10000 ≤ C₀ ∧ ∀ C ≥ C₀,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.IsAdmissible →
    2 ≤ Fintype.card ι → FullColRank I.A →
    let P := I.par C
    ∀ (ϵ ρ : ℝ) (x s : I.Vec) (τb : ι → ℝ), I.IsCentered P ϵ x s ρ →
    supNorm (fun i => (I.tau P x i)⁻¹ * (I.tau P x i - τb i)) ≤ P.α →
    let xf : I.Vec := x -
      (diagG (dim := I.dim) (fun i => (τb i)⁻¹) * I.hessInv x * I.A * (I.schur τb x)⁻¹) *ᵥ
        (I.Aᵀ *ᵥ x - I.b)
    I.Feasible xf ∧ (∃ y : Fin I.d → ℝ, I.A *ᵥ y + s = I.c) ∧
    ∀ y, I.Feasible y → I.c ⬝ᵥ xf ≤ 8 * ρ * I.d + I.c ⬝ᵥ y := by sorry

end BlockLewisIPM
