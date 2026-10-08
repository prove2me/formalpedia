-- Prove2me | Theorems.Thm_Cohen2019_Tight_radius_tight
-- name    : Cohen2019.Tight.radius_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:31:17.863023+00:00
-- url     : https://prove2.me/theorems/9c82c60e-b3ca-4bf4-a74f-7558a2fdf200
-- title:
--   Theorem 2 (corrected) — beyond the radius R some classifier consistent with (6) makes g(x + δ) ≠ c_A
-- statement:
--   Let $\sigma>0$, $x\in\mathbb R^d$, $c_A\in\mathcal Y$, and $0<\overline{p_B}\le\underline{p_A}<1$ with $\underline{p_A}+\overline{p_B}\le1$. Assume there are enough classes other than $c_A$: some finite set $s\subseteq\mathcal Y\setminus\{c_A\}$ has
--   $$1\le\underline{p_A}+|s|\,\overline{p_B}.$$
--   Let $R=\frac{\sigma}{2}\big(\Phi^{-1}(\underline{p_A})-\Phi^{-1}(\overline{p_B})\big)$. Then for every perturbation $\delta\in\mathbb R^d$ with $\|\delta\|_2>R$ there is a base classifier $f^*:\mathbb R^d\to\mathcal Y$ with Borel decision regions, consistent with the observed class probabilities (6),
--   $$\mathbb P(f^*(x+\varepsilon)=c_A)\ge\underline{p_A},\qquad \max_{c\ne c_A}\mathbb P(f^*(x+\varepsilon)=c)\le\overline{p_B},$$
--   and a class $c\ne c_A$ with
--   $$\mathbb P(f^*(x+\delta+\varepsilon)=c_A)<\mathbb P(f^*(x+\delta+\varepsilon)=c),\qquad\varepsilon\sim\mathcal N(0,\sigma^2I).$$
--   In particular, if $f^*$ is the base classifier of the smoothed classifier $g$, then $g(x+\delta)\ne c_A$ under any tie-breaking rule.
--
--   Together with Theorem 1 this says that, when only (6) is known about $f$, the $\ell_2$ ball of radius $R$ is exactly the set of perturbations that can be certified.
--
--   **Formalization Note.** As printed (with only $\underline{p_A}+\overline{p_B}\le1$), the theorem is false when $\mathcal Y$ has too few classes: for $\mathcal Y=\{c_A,c_B\}$, $\underline{p_A}=0.6$, $\overline{p_B}=0.1$, $\sigma=\|\delta\|=1$ one has $R\approx0.767<1$, yet every consistent $f$ has $\mathbb P(f(x+\varepsilon)=c_A)\ge0.9$ and Theorem 1 certifies radius $\Phi^{-1}(0.9)\approx1.28$. The capacity hypothesis restores it; with two classes it forces $\underline{p_A}+\overline{p_B}=1$. The witness is deterministic and may depend on $\delta$. $0<\overline{p_B}$ and $\underline{p_A}<1$ make $R$ a real number (otherwise the paper's $R$ is $+\infty$ or undefined and the theorem is vacuous); $\overline{p_B}\le\underline{p_A}$ is the middle link of (6).
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Theorem 2, p. 4; restated with proof, Appendix A, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, Theorem 2, p. 4, restated p. 15: "Assume
`p̲A + p̄B ≤ 1`. For any perturbation `δ ∈ ℝᵈ` with `‖δ‖₂ > R`, there exists a base classifier `f*`
consistent with the observed class probabilities (6) such that if `f*` is the base classifier for
`g`, then `g(x + δ) ≠ c_A`."

**Correction (class capacity).** As printed the theorem is false when `𝒴` has too few classes
(e.g. `𝒴 = {c_A, c_B}`, `p̲A = 0.6`, `p̄B = 0.1`, `σ = ‖δ‖ = 1`: `R ≈ 0.767 < 1`, yet every
consistent `f` has `ℙ(f(x + ε) = c_A) ≥ 0.9` and Theorem 1 certifies radius `Φ⁻¹(0.9) ≈ 1.28`).
The hypothesis `hcap` asks for a finite set `s` of classes other than `c_A` with
`1 ≤ p̲A + |s|·p̄B`; for two classes it forces `p̲A + p̄B = 1`.

The conclusion is the proof's strength: some class `c ≠ c_A` (the proof's `c_B`) is strictly more
likely than `c_A` under `𝒩(x + δ, σ²I)`, so `c_A` is not the argmax in (1) under any tie-breaking,
i.e. `g(x + δ) ≠ c_A`.

**Formalization Note.** The witness `f` is deterministic with Borel decision regions (a
deterministic classifier is in particular a random one). `0 < p̄B` and `p̲A < 1` are assumed so
that `R` is a real number: at `p̄B = 0` or `p̲A = 1` the paper's `R` is `+∞` and the theorem is
vacuous. `p̄B ≤ p̲A` is the middle link of (6). The classifier may depend on `δ`. -/
theorem radius_tight {d : ℕ} {Y : Type*} (σ : ℝ) (hσ : 0 < σ) (x : Space d) (cA : Y)
    (pA pB : ℝ) (hpB0 : 0 < pB) (hBA : pB ≤ pA) (hpA1 : pA < 1) (hsum : pA + pB ≤ 1)
    (hcap : ∃ s : Finset Y, cA ∉ s ∧ 1 ≤ pA + (s.card : ℝ) * pB)
    (δ : Space d) (hδ : radius σ pA pB < ‖δ‖) :
    ∃ f : Space d → Y, IsMeasurableClassifier f ∧ IsConsistent f σ x cA pA pB ∧
      ∃ c : Y, c ≠ cA ∧ classProb f σ (x + δ) cA < classProb f σ (x + δ) c := by sorry

end Cohen2019.Tight
