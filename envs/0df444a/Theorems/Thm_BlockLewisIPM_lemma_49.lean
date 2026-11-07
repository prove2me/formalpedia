-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_49
-- name    : BlockLewisIPM.lemma_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:17.612735+00:00
-- url     : https://prove2.me/theorems/312ca49a-9902-4541-942c-e980aa6fcaac
-- title:
--   Lemma 49 — the extended program: an explicit centered start, and transfer back (corrected: $\exists$ feasible point for the transfer)
-- statement:
--   Consider the program with $\|x\|_{2,\infty}\le R$ on $K$, $\|c\|_{2,\infty}\le L$ and $\max_i\|A_i\|_{\mathrm{op}}\le M$, with $L,R>0$ and accuracy $\delta>0$. Let $x^{(\mathrm{init})}$ minimize $\sum_i\phi_i$ over $\operatorname{int}K$, and consider the extended program
--
--   $$\min_{\tilde x\in K\times[0,2],\ \tilde A^\top\tilde x=b}\tilde c^\top\tilde x,\qquad \tilde A=\begin{bmatrix}A\\ b-A^\top x^{(\mathrm{init})}\end{bmatrix},\quad\tilde c=\begin{bmatrix}c\\ LR/\delta\end{bmatrix},$$
--
--   with barrier $\tilde\Phi([x,z])=\sum_i\phi_i(x_i)-\log z-\log(2-z)$.
--
--   1. If $\delta\le1/100$, the triplet $([x^{(\mathrm{init})};1],[c;LR/\delta],\ 5RmL/(d\delta^2))$ is $\delta$-centered for the extended program.
--   2. If the original program is feasible and $[x;z]$ is feasible and $\delta$-optimal for the extended program, then
--
--   $$c^\top x\le\min_{x\in K,\,A^\top x=b}c^\top x+\delta,\qquad \|A^\top x-b\|_\infty\le2mRM\Bigl(2m\delta+\frac{\delta^2}{LR}\Bigr).$$
--
--   This provides the initial point of the method and returns a solution of the extended program to the original one.
--
--   Differences from the source:
--   - correction: point 2 for every program → point 2 assumes ∃ y ∈ K with A⊤y = b; reason: the printed min over an empty set is undefined and the bound fails: m = n = d = 1, K₁ = [−1,1], A = (1), b = 2, c = 1, R = L = M = 1, δ = 1/100, x^(init) = 0 has extended optimum (x, z) = (1, 1/2) and |x − 2| = 1 > 0.0402
--   - reading: "δ-centered" with any δ > 0 → point 1 assumes δ ≤ 1/100; reason: Definition 17 defines ϵ-centered for ϵ ∈ (0, 1/100]
--   - reading: L, R ≥ 0 implicit → L, R > 0; reason: the formulas divide by LR
--   - reading: "x̄ ∈ K × [0,2]" in the second bullet → x̃ ∈ K × [0,2]; reason: a misprint: x̄ is not defined in the lemma
--   - reading: Ã with no rank condition → point 1 assumes full column rank of Ã; reason: Definition 13 uses P(·), defined for full column rank
--   - reading: min over the feasible set → ∀ feasible y, value ≤ δ + value at y; reason: no junk value of sInf; equal when the min exists
--   - reading: C universal → ∃ C₀ ≥ 10000, ∀ C ≥ C₀; reason: §3.1; the parameters at m + 1 blocks enter "δ-centered"
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 49, pp.44–45 and proof pp.89–90

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 49**, pp.44–45 (corrected: C4). Zhang, Wright, *A Fast Lewis-weight Interior Point Method
for Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** `xinit` is the minimizer of `∑ ϕ_i`, and `L, Rad > 0` since the formulas divide
by `LR`. Point 1 assumes `δ ≤ 1/100`, the range of "`δ`-centered" in Definition 17, and full column rank
of `Ã` (reading R10); centering is for the `m + 1` blocks of the extended program. Point 2 assumes the
program feasible (C4: at `K₁ = [-1,1]`, `A = (1)`, `b = 2`, `c = 1`, `R = L = M = 1`, `δ = 1/100`,
`xinit = 0` the extended optimum is `(1, 1/2)` and `|x - 2| = 1 > 0.0402`). `x̄` in the second bullet is
the page's misprint for `x̃`. `min` is read as `∀` feasible point (reading R7). `Rad` is the page's `R`. -/
theorem lemma_49 : ∃ C₀ : ℝ, 10000 ≤ C₀ ∧ ∀ C ≥ C₀,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.IsAdmissible →
    ∀ (δ Rad L M : ℝ), 0 < δ → 0 < Rad → 0 < L →
    (∀ i, ∀ x ∈ I.K i, ‖x‖ ≤ Rad) → (∀ i, eNorm (block I.c i) ≤ L) →
    (∀ i, opNorm (I.blockA i) ≤ M) →
    ∀ xinit : I.Vec, I.InDomain xinit →
    (∀ y : I.Vec, I.InDomain y →
      ∑ i, I.φ i (blockPt xinit i) ≤ ∑ i, I.φ i (blockPt y i)) →
    let E := I.extended xinit L Rad δ
    (δ ≤ 1 / 100 → FullColRank E.A →
      E.IsCentered (E.par C) δ (extVec xinit 1) (extVec I.c (L * Rad / δ))
        (5 * Rad * Fintype.card ι * L / (I.d * δ ^ 2))) ∧
    ((∃ y, I.Feasible y) → ∀ (x : I.Vec) (z : ℝ), E.Feasible (extVec x z) →
      (∀ y', E.Feasible y' → E.c ⬝ᵥ extVec x z ≤ δ + E.c ⬝ᵥ y') →
      (∀ y, I.Feasible y → I.c ⬝ᵥ x ≤ δ + I.c ⬝ᵥ y) ∧
      supNorm (I.Aᵀ *ᵥ x - I.b) ≤
        2 * Fintype.card ι * Rad * M * (2 * Fintype.card ι * δ + δ ^ 2 / (L * Rad))) := by sorry

end BlockLewisIPM
