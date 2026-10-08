-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_B_2
-- name    : AffinePSD.Necessity.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:32.460871+00:00
-- url     : https://prove2.me/theorems/47415c0d-1640-47cf-8c36-1a198ea3098b
-- title:
--   Lemma B.2 — for $u\in S_d^{++}$, $p_{k,\varepsilon}(e^{-\langle u,\cdot\rangle})<\infty$ and $e^{-\langle u,\cdot\rangle}|_{S_d^+}\in\mathcal S_+$
-- statement:
--   For $\varepsilon \ge 0$ and $k \ge 0$ let
--   $$p_{k,\varepsilon}(f) = \sup_{x \in S_d^+ + B_{\le\varepsilon}(0),\ |\alpha+\beta|\le k} \big|x^\alpha \partial^\beta f(x)\big|,$$
--   where $B_{\le \varepsilon}(0)$ is the closed $\varepsilon$-ball of $S_d$ and $\alpha, \beta$ are multi-indices in the $d(d+1)/2$ coordinates of $S_d$.
--
--   Let $u \in S_d^{++}$. Then for each $\varepsilon \ge 0$ and all $k \ge 0$,
--   $$p_{k,\varepsilon}\big(\exp(-\langle u, \cdot\rangle)\big) < \infty.$$
--   In particular $f_u := \exp(-\langle u,\cdot\rangle)|_{S_d^+} \in \mathcal S_+$; that is, $f_u = F_u|_{S_d^+}$ for some rapidly decreasing smooth function $F_u$ on $S_d$.
--
--   The exponentials $f_u$ are the test functions on which the generator is first computed; this lemma places them in the domain $\mathcal S_+$.
--
--   **Formalization Note.** The seminorms are replaced by the equivalent family $\sup (1+\|x\|)^k\, |D^j f(x)(e_1,\dots,e_j)|$ over symmetric $x$ within distance $\varepsilon$ of $S_d^+$, $j \le k$, and symmetric unit directions $e_m = \tfrac12(E^{ab}+E^{ba})$. For each fixed $\varepsilon$, finiteness for every $k$ is the same in both families. $\mathcal S$ is encoded by Schwartz functions on $M_d$, whose restrictions to $S_d^+$ are exactly $\mathcal S_+$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma B.2, p. 66; seminorms p_{k,ε} and (B.1), p. 65

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

open scoped SchwartzMap

namespace AffinePSD.Necessity

/-- Lemma B.2 (arXiv:0910.0137v3, App. B, p. 66). Let `u ∈ S_d^{++}`. Then for each `ε ≥ 0` and all
`k ≥ 0`, `p_{k,ε}(exp(−⟨u, ·⟩)) < ∞`. In particular `f_u := exp(−⟨u, ·⟩)|_{S_d^+} ∈ S_+`, that is,
`f_u = F_u|_{S_d^+}` for some `F_u ∈ S`.

**Formalization Note.** The seminorm `p_{k,ε}(f) = sup_{x ∈ S_d^+ + B_{≤ε}(0), |α+β| ≤ k} |x^α ∂^β f(x)|`
(p. 65) is replaced by the equivalent family
`sup_{x, j ≤ k} (1 + ‖x‖)^k |D^j f(x)(e_1, …, e_j)|` over symmetric `x` within `‖·‖`-distance `ε` of
`S_d^+` and symmetric unit directions `e_m = (E^{ab} + E^{ba})/2`; for each fixed `ε`, finiteness for all
`k` is the same in both families. `S` is encoded by Schwartz functions on `M_d` (their restrictions to
`S_d^+` are exactly `S_+`). -/
theorem lemma_B_2 {d : ℕ} (u : Mat d) (hu : PD u) :
    (∀ ε : ℝ, 0 ≤ ε → ∀ k : ℕ, ∃ C : ℝ, ∀ x : Mat d, IsSym x →
      (∃ y : Mat d, PSD y ∧ fnorm (x - y) ≤ ε) →
      ∀ j : ℕ, j ≤ k → ∀ v : Fin j → Fin d × Fin d,
        (1 + fnorm x) ^ k *
          |iteratedFDeriv ℝ j (fun z : Mat d => Real.exp (- tr u z)) x
            (fun m => symE (v m).1 (v m).2)| ≤ C) ∧
    ∃ F : 𝓢(Mat d, ℝ), ∀ x : Cone d, F x = Real.exp (- tr u x) := by sorry

end AffinePSD.Necessity
