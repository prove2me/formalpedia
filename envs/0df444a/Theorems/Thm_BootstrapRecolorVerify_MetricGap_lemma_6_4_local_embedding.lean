-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_lemma_6_4_local_embedding
-- name    : BootstrapRecolorVerify.MetricGap.lemma_6_4_local_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:43.69037+00:00
-- url     : https://prove2.me/theorems/b2116c0a-90e6-4810-a37b-631e3840e8de
-- title:
--   Lemma 6.4 — Local embedding
-- statement:
--   Fix an absolute spectral constant $C$ with the source's uniform success property. For every sufficiently large $r$, every $2\le i\le r$, every accepted hierarchy through stage $i$, and every subset $X\subseteq V(G_i)$ with $|X|\le n_{i-1}$, there exists a map $f:X\to\ell_1$ such that
--
--   $$\rho_i(u,v)\le\|f(u)-f(v)\|_1\le D\rho_i(u,v)\qquad(u,v\in X).$$
--
--   Here $\rho_i$ is the smooth cap (13) and $D=(1-(1-\epsilon)^L)^{-1}$. The size bound is the preceding cloud size. This statement gives the precise local metric embedding used by the recoloring estimate, including the source's distortion.
--
--   Differences from the source:
--   - generalization: one fixed absolute spectral constant C₁ supplied by Appendix B.1 → any fixed C satisfying the same uniform spectral-success property; reason: all estimates use only this property and a sufficiently-large threshold allowed to depend on C; the source constant is included
--   - generalization: the realization fixed after Claim 6.3 also has exceptional weighted-length increase at most 1 → every history satisfying the spectral and sampling acceptance events, without the exceptional-length bound; reason: Appendix B.4 and the proofs of Lemmas 6.5 and 6.7 do not use the length bound; every source realization satisfies these acceptance events, so the full source claim is included
--   - encoding: finite subsets X and maps into ℓ₁ → Finset subtypes and the real summable sequence space lp(ℕ,ℝ,1); reason: all subsets of the finite vertex set occur, including the empty set; the norm is the standard ℓ₁ norm
--   - encoding: the standing resampled hierarchy and sufficiently large r → Accepted C H and one threshold preceding r and every graph and subset; reason: the predicate contains only the actual spectral and sampling events from §6.3
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Lemma 6.4; Appendix B.4 p.33, p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=24; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Resampling

namespace BootstrapRecolorVerify.MetricGap

/-- Lemma 6.4 p.24, with all Part II standing conditions made explicit.
The size bound is the PREVIOUS CLOUD size, not the previous total vertex count. -/
theorem lemma_6_4_local_embedding (C : ℝ) (hC : IsSpectralConstant C) :
    ∃ R : ℕ, 3 ≤ R ∧ ∀ r ≥ R, ∀ i, 2 ≤ i → i ≤ r →
      ∀ H : History r i, Accepted C H →
        ∀ X : Finset (Vertex r i), X.card ≤ cloudSize r (i - 1) →
          ∃ f : X → lp (fun _ : ℕ => ℝ) 1,
            ∀ u v : X,
              rho H u v ≤ ‖f u - f v‖ ∧
              ‖f u - f v‖ ≤ distortion r * rho H u v := by sorry

end BootstrapRecolorVerify.MetricGap
