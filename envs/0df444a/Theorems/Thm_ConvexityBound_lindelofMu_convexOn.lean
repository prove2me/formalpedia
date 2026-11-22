-- Prove2me | Theorems.Thm_ConvexityBound_lindelofMu_convexOn
-- name    : ConvexityBound.lindelofMu_convexOn
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:46.347536+00:00
-- url     : https://prove2.me/theorems/6cc2baa1-a250-4983-a999-cfb836e00665
-- title:
--   Lindelöf's theorem: the $\mu$-function of a function of finite order in a vertical strip is finite, convex and continuous
-- statement:
--   **Lindelöf's convexity theorem for the $\mu$-function.** Let $I\subseteq\mathbb R$ be an open interval (bounded or unbounded), and let $f$ be a complex function which is *of finite order at large height* in the vertical strip $\{s\in\mathbb C:\operatorname{Re}(s)\in I\}$ in the following sense: for all $\sigma_1\le\sigma_2$ in $I$ there are real numbers $M$, $C$, $T$ such that at every $s$ with $\sigma_1\le\operatorname{Re}(s)\le\sigma_2$ and $|\operatorname{Im}(s)|\ge T$ the function $f$ is holomorphic and
--
--   $$|f(s)|\le C\,|\operatorname{Im}(s)|^{M}.$$
--
--   Let
--
--   $$\mu(\sigma)=\inf\bigl\{k\ge0:\ f(\sigma+it)=O(|t|^k)\ \text{as}\ |t|\to\infty\bigr\}$$
--
--   be the Lindelöf function of $f$. Then:
--
--   1. $\mu(\sigma)<\infty$ for every $\sigma\in I$;
--   2. $\mu$ is convex on $I$: for all $\sigma_1,\sigma_2\in I$ and $\theta\in[0,1]$,
--   $$\mu\bigl((1-\theta)\sigma_1+\theta\sigma_2\bigr)\le(1-\theta)\,\mu(\sigma_1)+\theta\,\mu(\sigma_2);$$
--   3. $\mu$ is continuous on $I$.
--
--   This is the classical consequence of the Phragmén–Lindelöf principle for functions of finite order in a strip. The source proves it as Lemma B.1.1.1, inequality (B.1.1.3), and applies it to a finite Hecke $L$-function: from $\mu(\sigma)=0$ for $\sigma>1$ and the bound on $\mu(\sigma)$ for $\sigma<0$ given by the functional equation it obtains the convexity bound of Proposition B.1.1.3.
--
--   **Deviation from the source.** Lemma B.1.1.1 of the source is stated for a half-plane $I=(a,\infty)$, for a meromorphic $f$ with finitely many simple poles, and with a polynomial bound that is uniform on the whole half-plane. These hypotheses imply the ones used here (a function with finitely many poles is holomorphic at large height). Neither the simplicity of the poles nor the uniformity over the whole half-plane is needed, and the statement is given for an arbitrary open interval $I$.
--
--   **Formalization Note.** `ConvexityBound.lindelofMu f σ` takes values in `ℝ≥0∞`; part 1 says that it is not `⊤` on $I$, and parts 2 and 3 are stated for the real-valued function `σ ↦ (lindelofMu f σ).toReal` with Mathlib's `ConvexOn ℝ I` and `ContinuousOn`. An open interval is encoded by `IsOpen I` together with `I.OrdConnected`, which covers bounded strips, half-planes and the whole plane.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 589, Lemma B.1.1.1, (B.1.1.2)-(B.1.1.3), with its proof on pp. 589-590; classical reference: E. C. Titchmarsh, The Theory of Functions, Oxford University Press, 1939, Ch. 9, §9.41 (convexity and continuity of $\mu$) and Ch. V, §5.65 (the Phragmén-Lindelöf interpolation step), as cited by the paper

import Mathlib
import Definitions.Def_ConvexityBound_LindelofMu

open scoped ENNReal

set_option autoImplicit false

namespace ConvexityBound

theorem lindelofMu_convexOn (f : ℂ → ℂ) (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected)
    (hf : ∀ σ₁ σ₂ : ℝ, σ₁ ∈ I → σ₂ ∈ I → σ₁ ≤ σ₂ →
      ∃ M C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
        DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M) :
    (∀ σ ∈ I, lindelofMu f σ ≠ ⊤) ∧
      ConvexOn ℝ I (fun σ : ℝ => (lindelofMu f σ).toReal) ∧
      ContinuousOn (fun σ : ℝ => (lindelofMu f σ).toReal) I := by sorry

end ConvexityBound
