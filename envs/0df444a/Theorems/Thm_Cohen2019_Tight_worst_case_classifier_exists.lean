-- Prove2me | Theorems.Thm_Cohen2019_Tight_worst_case_classifier_exists
-- name    : Cohen2019.Tight.worst_case_classifier_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:31:22.343598+00:00
-- url     : https://prove2.me/theorems/1a5d78e2-ecbd-4367-91f1-7686615f23de
-- title:
--   Proof of Theorem 2 — the worst-case classifier f* satisfies (6) with equalities
-- statement:
--   Let $\sigma>0$, $x,\delta\in\mathbb R^d$ with $\delta\ne0$, and $0<\overline{p_B}\le\underline{p_A}<1$ with $\underline{p_A}+\overline{p_B}\le1$. Let $c_A$ be a class and $s$ a finite set of classes with $c_A\notin s$, a class $c_B\in s$, and
--   $$1\le\underline{p_A}+|s|\,\overline{p_B}.$$
--   Then there is a base classifier $f^*:\mathbb R^d\to\mathcal Y$ with Borel decision regions such that
--
--   1. $f^*=c_A$ on $A$, $f^*=c_B$ on $B\setminus A$, and $f^*$ takes values in $s$ off $A$;
--   2. $\mathbb P(f^*(x+\varepsilon)=c_A)=\underline{p_A}$ and $\mathbb P(f^*(x+\varepsilon)=c_B)=\overline{p_B}$;
--   3. $\mathbb P(f^*(x+\varepsilon)=c)\le\overline{p_B}$ for every $c\ne c_A$.
--
--   This is the paper's $f^*$ ("$c_A$ if $x\in A$; $c_B$ if $x\in B$; other classes otherwise") with "other classes" made precise: the region between $A$ and $B$, of mass $1-\underline{p_A}-\overline{p_B}$, is assigned to classes of $s$ so that none receives more than $\overline{p_B}$.
--
--   **Formalization Note.** $\delta\ne0$ is added. The capacity condition on $s$ is the correction recorded for Theorem 2: without enough classes other than $c_A$, no classifier with these properties exists. When $\underline{p_A}+\overline{p_B}=1$, $A$ takes priority on the null hyperplane $A\cap B$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 2, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, proof of Theorem 2, p. 15: the classifier
`f*(z) = c_A` on `A`, `c_B` on `B`, "other classes otherwise" satisfies (6) with equalities,
`ℙ(f*(x + ε) = c_A) = ℙ(X ∈ A) = p̲A` and `ℙ(f*(x + ε) = c_B) = ℙ(X ∈ B) = p̄B`.

"Other classes otherwise" is made precise: the classes used off `A` lie in a finite set `s` of
classes other than `c_A`, containing `c_B`, large enough that `1 ≤ p̲A + |s|·p̄B`, and every class
other than `c_A` receives probability at most `p̄B` (which is what "satisfies (6)" requires). On
the null hyperplane `A ∩ B` (when `p̲A + p̄B = 1`) `A` takes priority.

**Formalization Note.** `δ ≠ 0` is added (the sets `A`, `B` are defined from `δ`), and
`0 < p̄B ≤ p̲A < 1` makes `Φ⁻¹(p̲A)`, `Φ⁻¹(1 − p̄B)` finite. The capacity hypothesis on `s` is the
correction recorded for Theorem 2; without enough other classes no such `f*` exists. -/
theorem worst_case_classifier_exists {d : ℕ} {Y : Type*} (x δ : Space d) (σ pA pB : ℝ)
    (hσ : 0 < σ) (hδ : δ ≠ 0) (cA cB : Y) (s : Finset Y) (hcA : cA ∉ s) (hcB : cB ∈ s)
    (hpB0 : 0 < pB) (hBA : pB ≤ pA) (hpA1 : pA < 1) (hsum : pA + pB ≤ 1)
    (hcap : 1 ≤ pA + (s.card : ℝ) * pB) :
    ∃ f : Space d → Y, IsMeasurableClassifier f ∧
      (∀ z ∈ setA x δ σ pA, f z = cA) ∧
      (∀ z ∈ setB x δ σ pB, z ∉ setA x δ σ pA → f z = cB) ∧
      (∀ z, z ∉ setA x δ σ pA → f z ∈ s) ∧
      classProb f σ x cA = pA ∧ classProb f σ x cB = pB ∧
      ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB := by sorry

end Cohen2019.Tight
