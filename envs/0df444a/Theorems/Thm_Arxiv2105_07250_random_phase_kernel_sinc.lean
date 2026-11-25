-- Prove2me | Theorems.Thm_Arxiv2105_07250_random_phase_kernel_sinc
-- name    : Arxiv2105_07250.random_phase_kernel_sinc
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:31:58.178805+00:00
-- url     : https://prove2.me/theorems/aa261d15-bcb4-4691-b14b-d40efddf13cd
-- title:
--   Eq. (14) (as proved): the stacking kernel of a band-limited random-phase source
-- statement:
--   Let $\tilde\omega_{\min}<\tilde\omega_{\max}$, $\Delta=\tilde\omega_{\max}-\tilde\omega_{\min}$, $\bar\omega=\frac12(\tilde\omega_{\max}+\tilde\omega_{\min})$ and $a\in\mathbb{R}$.
--
--   1. **(A31), as proved.** For $N\ge0$, let $\tilde\omega_j=\tilde\omega_{\min}+j\Delta/N$, $j=1,\dots,N$. Let $\theta_1,\dots,\theta_N$ be pairwise independent, each $\mathrm{Unif}(0,2\pi)$, and let $F(t')=\sum_{j=1}^N a\cos(\tilde\omega_jt'+\theta_j)$. Then for all $t',t''$:
--   $$\langle F(t')F(t'')\rangle=\frac{a^2}{2}\sum_{j=1}^N\cos\big(\tilde\omega_j(t''-t')\big).$$
--   2. **(A32).** For every $\tau$, $\frac1N\sum_{j=1}^N\cos(\tilde\omega_j\tau)\to\frac1\Delta\int_{\tilde\omega_{\min}}^{\tilde\omega_{\max}}\cos(w\tau)\,dw$ as $N\to\infty$.
--   3. **(A33)-(A34).** $\frac1\Delta\int_{\tilde\omega_{\min}}^{\tilde\omega_{\max}}\cos(w\tau)\,dw=\cos(\bar\omega\tau)\,\mathrm{sinc}(\tfrac12\Delta\tau)$, with $\mathrm{sinc}(x)=\sin x/x$ and $\mathrm{sinc}(0)=1$.
--   4. **(A35) and (14).** For $|v|>0$ and $\tau=(x''-x')/|v|$, this kernel equals $\cos\big(\bar\omega\frac{|x''-x'|}{|v|}\big)\,\mathrm{sinc}\big(\tfrac12\Delta\frac{|x''-x'|}{|v|}\big)$.
--   5. **Monochromatic limit.** For fixed $\bar\omega$ and $\tau$, $\cos(\bar\omega\tau)\,\mathrm{sinc}(\tfrac12\Delta\tau)\to\cos(\bar\omega\tau)$ as $\Delta\to0^+$.
--
--   **Formalization Note** As printed, (A31) has the factor $c_{\tilde\Omega}^2/|\tilde\Omega|$ and sums over $j=0,\dots,|\tilde\Omega|$. The arcsine means that the paper uses ($\langle\cos^2\theta\rangle=\langle\sin^2\theta\rangle=\frac12$, all other means zero) give the factor $a^2/2$ and the sum over $j=1,\dots,N$; item 1 states this. The normalisation $1/N$ of the paper's limit is placed in item 2. Eq. (14) also carries the factor $|\hat s(\omega)|^2$, which Appendix B does not derive. The kernel is therefore stated as the time-domain kernel of (A34), up to the paper's "proportional to", together with its spatial form (A35). The grid uses the right endpoints $\tilde\omega_{\min}+j\Delta/N$; the limit in item 2 is the same for any Riemann choice of points.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c007; Section 3, eq. (14), PDF p. 12; derivation in Appendix B, eqs. (A31)-(A35), PDF p. 39

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem random_phase_kernel_sinc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (wmin wmax : ℝ) (hw : wmin < wmax) (a : ℝ) :
    (∀ (N : ℕ) (θ : Fin N → Ω → ℝ), (∀ j, Measurable (θ j)) → (∀ j, P.map (θ j) = uniformPhase) →
      (∀ j k, j ≠ k → IndepFun (θ j) (θ k) P) → ∀ t' t'' : ℝ,
        ∫ r, sourceSignature (bandGrid wmin wmax N) (fun _ => a) (fun j => θ j r) t' *
            sourceSignature (bandGrid wmin wmax N) (fun _ => a) (fun j => θ j r) t'' ∂P =
          a ^ 2 / 2 * ∑ j, Real.cos (bandGrid wmin wmax N j * (t'' - t'))) ∧
    (∀ τ : ℝ, Tendsto (fun N : ℕ => (∑ j : Fin N, Real.cos (bandGrid wmin wmax N j * τ)) / N)
      atTop (𝓝 ((∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin)))) ∧
    (∀ τ : ℝ, (∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin) =
      Real.cos ((wmax + wmin) / 2 * τ) * Real.sinc ((wmax - wmin) / 2 * τ)) ∧
    (∀ vabs : ℝ, 0 < vabs → ∀ x' x'' : ℝ,
      Real.cos ((wmax + wmin) / 2 * ((x'' - x') / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * ((x'' - x') / vabs)) =
        Real.cos ((wmax + wmin) / 2 * (|x'' - x'| / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * (|x'' - x'| / vabs))) ∧
    (∀ w0 τ : ℝ, Tendsto (fun D : ℝ => Real.cos (w0 * τ) * Real.sinc (D / 2 * τ)) (𝓝[>] 0)
      (𝓝 (Real.cos (w0 * τ)))) := by sorry

end Arxiv2105_07250
