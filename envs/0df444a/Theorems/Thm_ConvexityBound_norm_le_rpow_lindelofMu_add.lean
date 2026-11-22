-- Prove2me | Theorems.Thm_ConvexityBound_norm_le_rpow_lindelofMu_add
-- name    : ConvexityBound.norm_le_rpow_lindelofMu_add
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:43.252512+00:00
-- url     : https://prove2.me/theorems/19e16a86-8d92-4f32-bb83-32c67d8e97ad
-- title:
--   Uniform growth bound $f(\sigma+it)=O_\varepsilon(|t|^{\mu(\sigma)+\varepsilon})$ on closed vertical strips
-- statement:
--   **Uniform growth with the Lindelöf exponent on closed strips.** Let $I\subseteq\mathbb R$ be an open interval (bounded or unbounded), and let $f$ be a complex function which is *of finite order at large height* in the vertical strip $\{s\in\mathbb C:\operatorname{Re}(s)\in I\}$ in the following sense: for all $\sigma_1\le\sigma_2$ in $I$ there are real numbers $M$, $C$, $T$ such that at every $s$ with $\sigma_1\le\operatorname{Re}(s)\le\sigma_2$ and $|\operatorname{Im}(s)|\ge T$ the function $f$ is holomorphic and
--
--   $$|f(s)|\le C\,|\operatorname{Im}(s)|^{M}.$$
--
--   Let
--
--   $$\mu(\sigma)=\inf\bigl\{k\ge0:\ f(\sigma+it)=O(|t|^k)\ \text{as}\ |t|\to\infty\bigr\}$$
--
--   be the Lindelöf function of $f$. Then for all $\sigma_1\le\sigma_2$ in $I$ and every $\varepsilon>0$ there are constants $C$ and $T$ such that
--
--   $$|f(\sigma+it)|\le C\,|t|^{\mu(\sigma)+\varepsilon}\qquad\text{for all }\sigma\in[\sigma_1,\sigma_2]\text{ and all real }t\text{ with }|t|\ge T .$$
--
--   In other words $f(\sigma+it)=O_{\varepsilon,\sigma_1,\sigma_2}(|t|^{\mu(\sigma)+\varepsilon})$ as $|t|\to\infty$, uniformly in $\sigma\in[\sigma_1,\sigma_2]$, although $\mu(\sigma)$ is defined line by line.
--
--   This is the last assertion of Lemma B.1.1.1 of the source. It is the form in which the Lindelöf function is used in practice: in the proof of the convexity bound (Proposition B.1.1.3) it converts the inequality $\mu(\sigma)\le[F:\mathbb Q]\,\frac{1-\sigma}{2}$ into a bound for the finite Hecke $L$-function that is uniform in $0\le\sigma\le1$.
--
--   **Deviation from the source.** Lemma B.1.1.1 of the source is stated for a half-plane $I=(a,\infty)$, for a meromorphic $f$ with finitely many simple poles, and with a polynomial bound that is uniform on the whole half-plane. These hypotheses imply the ones used here (a function with finitely many poles is holomorphic at large height). Neither the simplicity of the poles nor the uniformity over the whole half-plane is needed, and the statement is given for an arbitrary open interval $I$.
--
--   **Formalization Note.** `ConvexityBound.lindelofMu f σ` takes values in `ℝ≥0∞` and is finite on $I$ under these hypotheses (companion statement `ConvexityBound.lindelofMu_convexOn`); the exponent is `(lindelofMu f s.re).toReal + ε` and the power is the real power `Real.rpow`. The bound is asserted for $|\operatorname{Im}(s)|\ge T$ with $T$ depending on $\varepsilon,\sigma_1,\sigma_2$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 589, Lemma B.1.1.1 (last sentence: $f(\sigma+it)=O_{\varepsilon,\sigma_1,\sigma_2}(|t|^{\mu(\sigma)+\varepsilon})$ uniformly in $\sigma\in[\sigma_1,\sigma_2]$); classical reference: E. C. Titchmarsh, The Theory of Functions, Oxford University Press, 1939, Ch. 9, §9.41 and Ch. V, §5.65 (as cited by the paper)

import Mathlib
import Definitions.Def_ConvexityBound_LindelofMu

open scoped ENNReal

set_option autoImplicit false

namespace ConvexityBound

theorem norm_le_rpow_lindelofMu_add (f : ℂ → ℂ) (I : Set ℝ) (hI : IsOpen I)
    (hI' : I.OrdConnected)
    (hf : ∀ σ₁ σ₂ : ℝ, σ₁ ∈ I → σ₂ ∈ I → σ₁ ≤ σ₂ →
      ∃ M C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
        DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M)
    (σ₁ σ₂ : ℝ) (h₁ : σ₁ ∈ I) (h₂ : σ₂ ∈ I) (h₁₂ : σ₁ ≤ σ₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ ((lindelofMu f s.re).toReal + ε) := by sorry

end ConvexityBound
