-- Prove2me | Theorems.Thm_FoundationsML_Kernels_representer_theorem_v2
-- name    : FoundationsML.Kernels.representer_theorem_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:54.563242+00:00
-- url     : https://prove2.me/theorems/4be2d453-7a04-4214-90b7-062dadc1038d
-- title:
--   Theorem 6.11 — representer theorem (goal; corrected: a minimizer of the representer form exists whenever a minimizer exists)
-- statement:
--   **Statement (Theorem 6.11, p. 117, PDF p. 134; corrected form).** Let $K:X\times X\to\mathbb R$ be a PDS kernel and $H$ its corresponding RKHS. Then, for any non-decreasing function $G:\mathbb R\to\mathbb R$ and any loss function $L:\mathbb R^m\to\mathbb R\cup\{+\infty\}$, the optimization problem
--   $$\mathrm{argmin}_{h\in H} F(h) = \mathrm{argmin}_{h\in H} G(\|h\|_H) + L(h(x_1),\dots,h(x_m))$$
--   admits, whenever it admits a solution at all, a solution of the form $h^\star=\sum_{i=1}^m\alpha_i K(x_i,\cdot)$. If $G$ is further assumed to be increasing and $F$ is finite at some point, then any solution has this form.
--
--   **Formalization Note.** The retired version asserted unconditionally that a minimizer of the representer form exists, which is false: with $G\equiv0$ and a linear loss $F$ has no minimizer at all (the accepted disproof). This is an error in the printed statement, not in the proof: the proof shows only that for every $h$ its projection $h_1$ onto $\mathrm{span}\{K(x_i,\cdot)\}$ satisfies $F(h_1)\le F(h)$ (and $F(h_1)<F(h)$ when $G$ is increasing and $h\notin\mathrm{span}$), so the printed "admits a solution of the form" tacitly assumes the argmin is nonempty. The standard corrected reading is formalized: existence of some minimizer implies existence of one of the representer form. The second clause keeps the finiteness hypothesis $\exists h_0,\ F(h_0)\neq+\infty$, now placed where it is needed (for $L\equiv+\infty$ every $h$ minimizes $F\equiv+\infty$, so the clause would be false without it). $L$'s codomain $\mathbb R\cup\{+\infty\}$ is `WithTop ℝ`; $K(x_i,\cdot)$ is $\Phi(x_i)$ (Theorem 6.8's construction, with `ev h x = ⟨h, Φ x⟩`); non-decreasing/increasing are `Monotone`/`StrictMono`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 117, Theorem 6.11 (PDF p. 134) — corrected transcription of the first clause: existence of a representer-form minimizer is asserted conditionally on the existence of a minimizer

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS
import Definitions.Def_FoundationsML_Kernels_IsRKHSOf
import Definitions.Def_FoundationsML_Kernels_IsMinimizer

namespace FoundationsML.Kernels

/-- Theorem 6.11 (Representer theorem; goal; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 117, PDF p. 134), in its corrected form. Let
`K : X × X → ℝ` be a PDS kernel and `H` its corresponding RKHS. Then, for any non-decreasing
function `G : ℝ → ℝ` and any loss function `L : ℝ^m → ℝ ∪ {+∞}`, the optimization problem
`argmin_{h∈H} F(h) = argmin_{h∈H} G(‖h‖_H) + L(h(x_1),…,h(x_m))`, whenever it admits a
solution, admits a solution of the form `h* = ∑_{i=1}^m α_i K(x_i,·)`. If `G` is further
assumed to be increasing and `F` is finite somewhere, then any solution has this form.

**Formalization Note.** Replaces `representer_theorem`, whose first clause asserted
unconditionally that a minimizer of the stated form exists, which is false (disproved with
`G ≡ 0` and a linear loss, where `F` has no minimizer at all). The book's proof shows only
that for every `h` the projection `h_1` of `h` onto `span{K(x_i,·)}` satisfies `F(h_1) ≤ F(h)`
(and `F(h_1) < F(h)` when `G` is increasing and `h ∉ span`), so the printed "admits a
solution of the form" tacitly assumes the argmin is nonempty; this is the standard corrected
reading and is what is formalized: existence of some minimizer implies existence of one of
the representer form. The second clause keeps the finiteness hypothesis `∃ h₀, F h₀ ≠ ⊤`
(now placed where it is needed): for `L ≡ +∞` every `h` minimizes `F ≡ ⊤`, so the clause
would be false without it. `L`'s codomain `ℝ ∪ {+∞}` is `WithTop ℝ`; `K(x_i,·)` is `Φ (x i)`
(Theorem 6.8's construction); non-decreasing/increasing are `Monotone`/`StrictMono`. -/
theorem representer_theorem_v2
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (hK : IsPDS K) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev)
    (m : ℕ) (x : Fin m → X)
    (G : ℝ → ℝ) (hG : Monotone G)
    (L : (Fin m → ℝ) → WithTop ℝ)
    (F : H → WithTop ℝ) (hF : ∀ h : H, F h = (G ‖h‖ : WithTop ℝ) + L (fun i => ev h (x i))) :
    ((∃ h : H, IsMinimizer F h) → ∃ α : Fin m → ℝ, IsMinimizer F (∑ i, α i • Φ (x i))) ∧
    (StrictMono G → (∃ h₀ : H, F h₀ ≠ ⊤) →
      ∀ h : H, IsMinimizer F h → ∃ α : Fin m → ℝ, h = ∑ i, α i • Φ (x i)) := by sorry

end FoundationsML.Kernels
