-- Prove2me | Theorems.Thm_APSCounting893_Main_puiseux_integral_embedding
-- name    : APSCounting893.Main.puiseux_integral_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:23:59.950496+00:00
-- url     : https://prove2.me/theorems/d079f61a-9079-4eb7-9f83-2832150a268b
-- title:
--   Lemma 4.4 — Embedding into the Puiseux field
-- statement:
--   For every Galois extension $M/\mathbb C(t)$, the natural inclusion extends to an embedding $M\hookrightarrow\mathcal K$, where $\mathcal K$ is the Puiseux algebraic closure of $\mathbb C((t))$. Every such embedding sends the integral closure of $\mathbb C[t]$ in $M$ into $\mathcal O_{\mathcal K}$. In addition,
--
--   $$\mathcal O_{\mathcal K}\text{ is integrally closed}.$$
--
--   The inclusion is pinned by constants and the image of $t$. The statement permits every Galois extension and does not assume unramifiedness or a fixed ramification denominator.
--
--   Differences from the source:
--   - encoding: an embedding into the Puiseux field and integrally closed valuation ring → an ambient Hahn-series algebra embedding with every image element in the Puiseux union, and the monic-root criterion inside that union; reason: this is exactly an embedding into the source field and the elementwise definition of integral closedness
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 4.4, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem puiseux_integral_embedding (M : Type) [Field M] [Algebra ℂ M] [Algebra (RatFunc ℂ) M]
    [IsScalarTower ℂ (RatFunc ℂ) M] [IsGalois (RatFunc ℂ) M] :
    let tM := algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
    let t := HahnSeries.single (1 : ℚ) (1 : ℂ)
    (∃ rho : M →ₐ[ℂ] PuiseuxAmbient, rho tM = t ∧ ∀ z, IsPuiseux (rho z)) ∧
    (∀ rho : M →ₐ[ℂ] PuiseuxAmbient, rho tM = t → (∀ z, IsPuiseux (rho z)) →
      ∀ z : M,
        (∃ p : Polynomial (Polynomial ℂ), p.Monic ∧
          Polynomial.eval₂
            ((algebraMap (RatFunc ℂ) M).comp
              (algebraMap (Polynomial ℂ) (RatFunc ℂ))) z p = 0) →
        PuiseuxIntegral (rho z)) ∧
    (∀ z : PuiseuxAmbient, IsPuiseux z →
      (∃ p : Polynomial PuiseuxAmbient, p.Monic ∧
        (∀ i, PuiseuxIntegral (p.coeff i)) ∧ Polynomial.eval z p = 0) → PuiseuxIntegral z) := by sorry

end APSCounting893.Main
