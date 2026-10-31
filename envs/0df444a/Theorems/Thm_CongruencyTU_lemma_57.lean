-- Prove2me | Theorems.Thm_CongruencyTU_lemma_57
-- name    : CongruencyTU.lemma_57
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:54.426372+00:00
-- url     : https://prove2.me/theorems/3c633623-cdd4-472a-bc8f-2a8b61f0b735
-- title:
--   Lemma 57 (Averaging Lemma): two relaxed solutions of (1) re-split into two solutions with averaged scalar products
-- statement:
--   Consider the relaxation of an R-CCTUF problem of form (1). Let $x^1$ and $x^2$ be solutions for $(\alpha_1,\beta_1)$ and $(\alpha_2,\beta_2)$, i.e. $f^\top x^j_B=\alpha_j$ and $h^\top x^j_A=\beta_j$. Then there exist solutions $x^3$ and $x^4$ for $(\alpha_3,\beta_3)$ and $(\alpha_4,\beta_4)$ such that $x^1+x^2=x^3+x^4$ and, for $j\in\{3,4\}$,
--   $$\Big\lfloor\tfrac{\alpha_1+\alpha_2}2\Big\rfloor\le\alpha_j\le\Big\lceil\tfrac{\alpha_1+\alpha_2}2\Big\rceil,\qquad\Big\lfloor\tfrac{\beta_1+\beta_2}2\Big\rfloor\le\beta_j\le\Big\lceil\tfrac{\beta_1+\beta_2}2\Big\rceil,$$
--   $$\Big\lfloor\tfrac{\alpha_1+\beta_1+\alpha_2+\beta_2}2\Big\rfloor\le\alpha_j+\beta_j\le\Big\lceil\tfrac{\alpha_1+\beta_1+\alpha_2+\beta_2}2\Big\rceil.$$
--
--   The lemma relates the residues of the B-problem at neighbouring pairs $(\alpha,\beta)$, which forces patterns with singleton values to be linear.
--
--   **Formalization Note** Floors and ceilings are taken in $\mathbb Q$.
--
--   Differences from the source:
--
--   - reading: "an R-CCTUF problem of the form given in (1)" → a Form1 whose two 3-sum summands (A e e; h⊤ 0 1) and (0 1 f⊤; g g B) are totally unimodular (zero vectors for 1- and 2-sums), with m > 0 and R ⊆ {0, …, m − 1}; reason: form (1) is introduced for case (iii) of Theorem 14, a decomposition into totally unimodular summands (p.9); the 3-sum of TU summands is TU (p.8)
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.39 (PDF p.40), Lemma 57, display (23)

import Mathlib
import Definitions.Def_CongruencyTU_Pattern

open Matrix

namespace CongruencyTU

/-- **Lemma 57 (Averaging Lemma)** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.39, PDF p.40): "Consider the relaxation of an R-CCTUF
problem of the form given in (1). Let x¹ and x² be solutions for (α₁, β₁) and (α₂, β₂),
respectively. Then, there exist solutions x³ and x⁴ for (α₃, β₃) and (α₄, β₄), respectively, such
that x¹ + x² = x³ + x⁴, as well as ⌊(α₁+α₂)/2⌋ ≤ α₃, α₄ ≤ ⌈(α₁+α₂)/2⌉,
⌊(β₁+β₂)/2⌋ ≤ β₃, β₄ ≤ ⌈(β₁+β₂)/2⌉, and
⌊(α₁+β₁+α₂+β₂)/2⌋ ≤ α₃+β₃, α₄+β₄ ≤ ⌈(α₁+β₁+α₂+β₂)/2⌉. (23)"

A solution for `(α, β)` is a solution `(x_A, x_B)` of the relaxation of (1) with `f⊤x_B = α` and
`h⊤x_A = β` (p.39).

**Formalization Note.** Form (1) is a `Form1` with totally unimodular summands (case (iii) of
Theorem 14). Floors and ceilings of halves are taken in `ℚ`. -/
theorem lemma_57 (F : Form1) (hF : F.Valid) (α₁ β₁ α₂ β₂ : ℤ)
    (x₁A : Fin F.nA → ℤ) (x₁B : Fin F.nB → ℤ) (x₂A : Fin F.nA → ℤ) (x₂B : Fin F.nB → ℤ)
    (h₁ : F.Relaxed x₁A x₁B) (h₁' : F.For α₁ β₁ x₁A x₁B)
    (h₂ : F.Relaxed x₂A x₂B) (h₂' : F.For α₂ β₂ x₂A x₂B) :
    ∃ (α₃ β₃ α₄ β₄ : ℤ) (x₃A : Fin F.nA → ℤ) (x₃B : Fin F.nB → ℤ)
      (x₄A : Fin F.nA → ℤ) (x₄B : Fin F.nB → ℤ),
      F.Relaxed x₃A x₃B ∧ F.For α₃ β₃ x₃A x₃B ∧ F.Relaxed x₄A x₄B ∧ F.For α₄ β₄ x₄A x₄B ∧
      x₁A + x₂A = x₃A + x₄A ∧ x₁B + x₂B = x₃B + x₄B ∧
      (⌊((α₁ + α₂ : ℤ) : ℚ) / 2⌋ ≤ α₃ ∧ α₃ ≤ ⌈((α₁ + α₂ : ℤ) : ℚ) / 2⌉) ∧
      (⌊((α₁ + α₂ : ℤ) : ℚ) / 2⌋ ≤ α₄ ∧ α₄ ≤ ⌈((α₁ + α₂ : ℤ) : ℚ) / 2⌉) ∧
      (⌊((β₁ + β₂ : ℤ) : ℚ) / 2⌋ ≤ β₃ ∧ β₃ ≤ ⌈((β₁ + β₂ : ℤ) : ℚ) / 2⌉) ∧
      (⌊((β₁ + β₂ : ℤ) : ℚ) / 2⌋ ≤ β₄ ∧ β₄ ≤ ⌈((β₁ + β₂ : ℤ) : ℚ) / 2⌉) ∧
      (⌊((α₁ + β₁ + α₂ + β₂ : ℤ) : ℚ) / 2⌋ ≤ α₃ + β₃ ∧
        α₃ + β₃ ≤ ⌈((α₁ + β₁ + α₂ + β₂ : ℤ) : ℚ) / 2⌉) ∧
      (⌊((α₁ + β₁ + α₂ + β₂ : ℤ) : ℚ) / 2⌋ ≤ α₄ + β₄ ∧
        α₄ + β₄ ≤ ⌈((α₁ + β₁ + α₂ + β₂ : ℤ) : ℚ) / 2⌉) := by sorry

end CongruencyTU
