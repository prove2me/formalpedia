-- Prove2me | Theorems.Thm_DeepSets_Supplement_theorem_7_continuous_sum_decomposition
-- name    : DeepSets.Supplement.theorem_7_continuous_sum_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:27:00.33823+00:00
-- url     : https://prove2.me/theorems/d3b8c4df-d099-5a13-aef9-dcd891a80140
-- title:
--   Theorem 7 — at a fixed size, continuous and permutation invariant on $[0,1]^M$ iff $f=\rho\left(\sum_m\phi(x_m)\right)$ with $\phi$ independent of $f$
-- statement:
--   Fix a set size $M\ge 0$.
--
--   1. A function $f:[0,1]^M\to\mathbb R$ is permutation invariant and continuous if and only if there are continuous functions $\phi:\mathbb R\to\mathbb R^{M+1}$ (inner) and $\rho:\mathbb R^{M+1}\to\mathbb R$ (outer) with
--   $$
--   f(x_1,\dots,x_M)=\rho\Bigl(\sum_{m=1}^{M}\phi(x_m)\Bigr)\qquad\text{for all }(x_1,\dots,x_M)\in[0,1]^M .
--   $$
--   2. The inner function is independent of $f$: there is one continuous $\phi:\mathbb R\to\mathbb R^{M+1}$ such that every continuous permutation-invariant $f$ on $[0,1]^M$ has this representation with that $\phi$ and some continuous $\rho:\mathbb R^{M+1}\to\mathbb R$.
--
--   This is the uncountable counterpart of Theorem 2 at a fixed set size: continuity is kept on both sides, at the price of a latent space of dimension $M+1$. It is a companion theorem and is not used in the proof of Theorem 2.
--
--   **Formalization Note** $f$ is a function on $\mathbb R^M$ of which only the values on the cube matter: continuity on the cube (`ContinuousOn`), invariance on the cube, repeated entries included, and equality on the cube. The functions $\phi$ and $\rho$ are continuous on the whole of their domains.
--
--   Differences from the source:
--   - reading: "Let f : [0,1]^M → ℝ be a permutation invariant continuous function iff it has the representation (18)" → f is permutation invariant and continuous on [0,1]^M iff it has the representation (18) for some continuous φ and ρ; reason: the printed sentence is garbled ("Let … iff"); the proof opens with sufficiency and then proves necessity for all permutation invariant continuous functions, so continuity and invariance are the left side of the iff
--   - reading: "The inner function φ is independent of the function f" → a second conjunct: there is one continuous φ, chosen before f, that serves every continuous invariant f; reason: this is the meaning of the sentence, and the proof uses φ(x) = [1, x, …, x^M] for every f
--   - encoding: f : [0,1]^M → ℝ → f on Fin M → ℝ, with continuity, invariance and equation (18) required on the cube only; reason: Lean convention; every function on the cube is such a restriction, and values outside the cube are unconstrained
--   - encoding: a fixed set size M, ρ : ℝ^{M+1} → ℝ, φ : ℝ → ℝ^{M+1} → any M : ℕ (M = 0 included), ℝ^{M+1} as Fin (M + 1) → ℝ; reason: the page excludes no set size; same instances
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, Theorem 7, eq. (18), p.14 (PDF p.14); proof pp.14-15

import Mathlib
import Definitions.Def_DeepSets_Supplement_IsPermInvariantOn

namespace DeepSets.Supplement

/-- **Theorem 7** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.2, p.14). A function
`f : [0,1]^M → ℝ` is permutation invariant and continuous iff it has the representation
`f(x₁, …, x_M) = ρ(∑_{m=1}^M φ(x_m))` (18) for some continuous outer and inner functions
`ρ : ℝ^{M+1} → ℝ` and `φ : ℝ → ℝ^{M+1}`. The inner function `φ` is independent of the function `f`.

**Formalization Note**
* The page prints "Let f … be a permutation invariant continuous function iff …". It is read as
  the iff above, as its proof confirms (sufficiency, then necessity): continuity and invariance
  are on the left of the iff.
* The first conjunct is the iff. The second is the last sentence: one continuous `φ` is chosen
  before `f`, and only `ρ` depends on `f`.
* `f` is a function on `Fin M → ℝ` of which only the values on the cube `[0,1]^M` matter. Its
  continuity (`ContinuousOn`), its invariance and the representation are all on the cube.
  `φ` and `ρ` are continuous on the whole of `ℝ` and of `ℝ^{M+1}`, as printed. -/
theorem theorem_7_continuous_sum_decomposition (M : ℕ) :
    (∀ f : (Fin M → ℝ) → ℝ,
      (IsPermInvariantOn (Set.Icc (0 : ℝ) 1) f ∧
        ContinuousOn f (Set.univ.pi fun _ : Fin M => Set.Icc (0 : ℝ) 1)) ↔
      ∃ (φ : ℝ → Fin (M + 1) → ℝ) (ρ : (Fin (M + 1) → ℝ) → ℝ),
        Continuous φ ∧ Continuous ρ ∧
          ∀ x ∈ Set.univ.pi (fun _ : Fin M => Set.Icc (0 : ℝ) 1), f x = ρ (∑ m, φ (x m))) ∧
    (∃ φ : ℝ → Fin (M + 1) → ℝ, Continuous φ ∧
      ∀ f : (Fin M → ℝ) → ℝ,
        IsPermInvariantOn (Set.Icc (0 : ℝ) 1) f →
        ContinuousOn f (Set.univ.pi fun _ : Fin M => Set.Icc (0 : ℝ) 1) →
        ∃ ρ : (Fin (M + 1) → ℝ) → ℝ, Continuous ρ ∧
          ∀ x ∈ Set.univ.pi (fun _ : Fin M => Set.Icc (0 : ℝ) 1), f x = ρ (∑ m, φ (x m))) := by sorry

end DeepSets.Supplement
