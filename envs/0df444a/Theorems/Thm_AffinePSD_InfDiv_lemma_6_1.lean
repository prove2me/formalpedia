-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_lemma_6_1
-- name    : AffinePSD.InfDiv.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:48.86629+00:00
-- url     : https://prove2.me/theorems/6e791b0d-5f01-44c5-aca9-5210d7eabe23
-- title:
--   Lemma 6.1 — an additive $g:S_d^+\to\mathbb R$ extends additively to $S_d$; if measurable, it is $\langle c,\cdot\rangle$
-- statement:
--   Let $g:S_d^+\to\mathbb R$ be **additive**, that is, $g$ satisfies Cauchy's functional equation
--   $$g(x+y)=g(x)+g(y),\qquad x,y\in S_d^+.\qquad(6.4)$$
--   Then $g$ extends to an additive function $f:S_d\to\mathbb R$. If moreover $g$ is measurable on $S_d^+$, then $f$ is measurable on $S_d$ and is a continuous linear functional:
--   $$f(x)=\langle c,x\rangle\quad\text{for all }x\in S_d,\ \text{for some }c\in S_d.$$
--
--   This is the linear-algebra step behind Lemma 6.2. Positive semidefinite matrices span $S_d$, so a measurable additive function on the cone is the restriction of a linear functional.
--
--   **Formalization Note** $f$ is a function on $M_d$. Only its restriction to the symmetric matrices is constrained: additivity, measurability (on the subtype of symmetric matrices) and the linear form are all stated on $S_d$. The additive extension is unique, so the existential names the paper's $f$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §6.3, Lemma 6.1, (6.4), p. 54

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone

namespace AffinePSD.InfDiv

/-- Lemma 6.1 (arXiv:0910.0137v3, §6.3, p. 54). Let `g : S_d^+ → ℝ` be additive,
`g(x + y) = g(x) + g(y)` (6.4). Then `g` extends to an additive `f : S_d → ℝ`; if moreover `g` is
measurable, then `f` is measurable on `S_d` and `f(x) = ⟨c, x⟩` for some `c ∈ S_d`.
Formalization Note: `f` is a function on `Mat d`; only its restriction to the symmetric
matrices `S_d` is constrained (additivity, measurability and the linear form are all stated on
`S_d`). The additive extension is unique, so the existential names the paper's `f`. -/
theorem lemma_6_1 {d : ℕ} (g : AffinePSD.Necessity.Cone d → ℝ) (hg : ∀ x y : AffinePSD.Necessity.Cone d, g (coneAdd x y) = g x + g y) :
    ∃ f : AffinePSD.Necessity.Mat d → ℝ,
      (∀ x y : AffinePSD.Necessity.Mat d, AffinePSD.Necessity.IsSym x → AffinePSD.Necessity.IsSym y → f (x + y) = f x + f y) ∧
      (∀ x : AffinePSD.Necessity.Cone d, f x.1 = g x) ∧
      (Measurable g →
        Measurable (fun x : {x : AffinePSD.Necessity.Mat d // AffinePSD.Necessity.IsSym x} => f x.1) ∧
        ∃ c : AffinePSD.Necessity.Mat d, AffinePSD.Necessity.IsSym c ∧ ∀ x : AffinePSD.Necessity.Mat d, AffinePSD.Necessity.IsSym x → f x = AffinePSD.Necessity.tr c x) := by sorry

end AffinePSD.InfDiv
