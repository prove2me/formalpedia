-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_smoothing
-- name    : BrickworkPorterThomas.Convergence.smoothing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:02.530085+00:00
-- url     : https://prove2.me/theorems/ce03d85b-015c-407f-9223-eb1eaa7c6096
-- title:
--   Theorem 5.1 — band-limited smoothing of the circuit output density
-- statement:
--   For every constant $a>0$ there is a constant $a'>a$, independent of $n$ and $\varepsilon$, such that the following holds. Let $U\sim\mathcal C(l)$ be a brickwork Haar random circuit on $n$ qubits ($n$ even, $d=2^n$), let $b\in\{0,1\}^n$, and let $F=|\langle b|U|0^n\rangle|^2$. Suppose that $F$ has a probability density $f$ that is monotone decreasing and absolutely continuous on $[0,1]$, with $\|f'\|_{L^1}=a\,d$. Then for every $0<\varepsilon<1$ there is a probability density $f_*\in C^\infty(\mathbb R)$ such that
--
--   $$
--   d_{TV}(f,f_*)\le\varepsilon\qquad\text{and}\qquad\hat f_*(s)=0\ \text{ for all } |s|>\frac{a'd}{\varepsilon}.
--   $$
--
--   The smoothed density has a band-limited characteristic function, which removes the high-frequency part of the Fourier integral in the main proof.
--
--   **Formalization Note** "$f$ is the density of $F$" means that the law of $F$ is $f(x)\,dx$ with $f\ge0$ measurable. Monotonicity and absolute continuity are imposed on $[0,1]$, and $\|f'\|_{L^1}=\int_0^1|f'|$. The source's "for every integer $k\ge1$" quantifies a variable that does not occur in the conclusion and is omitted.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: layers numbered 1..l, odd layers on (1,2),(3,4),…, even layers on (2,3),…,(n,1) → layers numbered 0..l−1 with the pairs of the reused brickPair (Lean layer j is the source layer j+1); reason: index shift only; the pairs and the chronological order are the source’s
--   - encoding: for every integer k ≥ 1 and every 0 < ε < 1 → for every 0 < ε < 1; reason: k does not occur in the hypotheses or the conclusion
--   - encoding: f the pdf of F, monotone decreasing and absolutely continuous, ‖f′‖_{L¹} = a d → a measurable f ≥ 0 with law(F) = f(x)dx, antitone and absolutely continuous on [0,1], ∫₀¹|f′| = a d; reason: a density lives on its natural interval [0,1]; global monotonicity on ℝ is impossible for a density
--   - encoding: a′ > a > 0 constants independent of n and ε → ∀ a > 0, ∃ a′ > a before n, l, b, f, ε; reason: quantifier order of the source’s constants
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §5, p. 14, Theorem 5.1, Eqs. (84)–(85); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit
import Definitions.Def_BrickworkPorterThomas_Convergence_Densities

namespace BrickworkPorterThomas.Convergence

open MeasureTheory

/-- Theorem 5.1 (p. 14). For every constant `a > 0` there is a constant `a' > a` (independent of
`n` and `ε`) such that: if the law of `F = |⟨b|U|0^n⟩|²`, `U ∼ C(l)` on `n = 2M` qubits, has a
density `f` that is monotone decreasing and absolutely continuous on `[0,1]` with
`‖f'‖_{L¹} = a d` (`d = 2^n`), then for every `0 < ε < 1` there is a `C^∞` probability density
`f_*` with `d_TV(f, f_*) ≤ ε` and `f̂_*(s) = 0` for all `|s| > a' d / ε`. -/
theorem smoothing : ∀ a : ℝ, 0 < a → ∃ a' : ℝ, a < a' ∧
    ∀ (M l : ℕ) (b : Bits (2 * M)) (f : ℝ → ℝ), 1 ≤ M →
      Measurable f → (∀ x, 0 ≤ f x) → outputLaw M l b = densityLaw f →
      AntitoneOn f (Set.Icc 0 1) → AbsolutelyContinuousOnInterval f 0 1 →
      ∫ x in (0 : ℝ)..1, |deriv f x| = a * (2 : ℝ) ^ (2 * M) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ fs : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fs ∧ IsDensity fs ∧
          dTV f fs ≤ ε ∧
          ∀ s : ℝ, a' * (2 : ℝ) ^ (2 * M) / ε < |s| → charDensity fs s = 0 := by sorry

end BrickworkPorterThomas.Convergence
