-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_G_1
-- name    : CondGeoVerif.Supplement.theorem_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:19:25.783744+00:00
-- url     : https://prove2.me/theorems/c16bf0fa-f890-4a4d-b334-0cf18e19f658
-- title:
--   Theorem G.1 (= Theorem 5.1) — homogeneous halfspaces under unknown smooth feature laws $\mathcal D_{\tau_a}$ with $m_V=O_a((\sqrt d/\varepsilon)\log(e/(\varepsilon\delta)))$
-- statement:
--   Let $a^\dagger$ be the threshold of Theorem D.2. For $0\le\tau<1$, $\mathcal D_\tau$ is the set of centered isotropic laws on $\mathbb R^d$ with a positive density $Z^{-1}e^{-V}$, $V\in C^2$, $(1-\tau)I_d\preceq\nabla^2V\preceq(1+\tau)I_d$. Completeness permits every Massart labeling with signal floor $a$ ($\mathbb E[Y\mid X]=b(X)\,\mathrm{sign}(w\cdot X)$, $a\le b(X)\le1$) and soundness every measurable labeling, both under a feature marginal in $\mathcal D_\tau$.
--
--   For every fixed $a\in(a^\dagger,1)$ there is $\tau_a>0$, independent of $d,\varepsilon,\delta$, with the following property. Uniformly over unknown marginals in $\mathcal D_{\tau_a}$, there is a one-message proper verifier with full Massart completeness, arbitrary-label soundness, and error at most $\delta$, using
--   $$m_V=O_a\Big(\frac{\sqrt d}\varepsilon\log\frac e{\varepsilon\delta}\Big),\qquad m_P=O_a\Big(\frac{d\log(e/\varepsilon)+\log(e/(\varepsilon\delta))}{\varepsilon^2}\Big).$$
--   It outputs a candidate whose risk is at most the best homogeneous halfspace risk plus $\varepsilon$, or rejects. The message consists of the candidate and $O(\log(e/\varepsilon))$ orthonormal frames, each of dimension at most a constant $K_a$; it contains no description of the unknown density or its conditional means.
--
--   Differences from the source:
--   - encoding: a† the threshold of Theorem D.2 → any η† ∈ (0, 1/2) with J_{η†} = 0, and a ∈ (1 − 2η†, 1); reason: the zero is unique by Theorem D.2
--   - encoding: density Z⁻¹e^{−V} → Lebesgue density e^{−V} of a probability measure, Hessian bound on the quadratic form, with finite second moments; reason: Z is absorbed into V without changing ∇²V; finite second moments follow from the lower Hessian bound for τ < 1
--   - encoding: signal floor a → Massart noise ≤ (1 − a)/2 relative to the feature marginal; reason: P(Y ≠ sign(w·X) | X) = (1 − b(X))/2
--   - encoding: the message: the candidate and O(log(e/ε)) frames of dimension ≤ K_a → message type ℝ^d × (Fin N → FrameMsg d K_a), N ≤ C log(e/ε); every output is the halfspace of the unit candidate and every frame of an accepted message is orthonormal; reason: the paper's message, made a type; no density is in it
--   - encoding: ranges of ε, δ → 0 < ε < 1, 0 < δ ≤ 1/4; reason: the paper's standing ranges (§2, p.3)
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem G.1 and (G.1), p.57 (PDF p.60); formal version of Theorem 5.1 and (5.1), p.11 (PDF p.14)

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_Mhalf
import Definitions.Def_CondGeoVerif_Supplement_IsSmoothIsoLaw

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem G.1** (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, p.57 = PDF p.60; the formal version of Theorem 5.1, p.11). Let
`a†` be the threshold in Theorem D.2. For every fixed `a ∈ (a†, 1)` there is `τ_a > 0`, independent
of `d, ε, δ`, with the following property. Uniformly over unknown feature marginals in `D_{τ_a}`
(centered isotropic laws with density `∝ e^{−V}`, `(1 − τ_a)I ⪯ ∇²V ⪯ (1 + τ_a)I`), there is a
one-message proper verifier for homogeneous halfspaces with full Massart completeness of signal
floor `a`, arbitrary-label soundness, and error at most `δ`, using
`m_V = O_a((√d/ε) log(e/(εδ)))` and `m_P = O_a((d log(e/ε) + log(e/(εδ)))/ε²)`. It outputs a
candidate whose risk is at most the best homogeneous halfspace risk plus `ε`, or rejects. The message
consists of the candidate and `O(log(e/ε))` orthonormal frames, each of dimension at most a constant
`K_a`; it contains no description of the unknown density or its conditional means.

**Formalization Note** `a†` enters through `η†`'s defining property (a zero of `J` in `(0, 1/2)`,
unique by Theorem D.2). Signal floor `a` is Massart noise `≤ (1 − a)/2` relative to the feature law
(`E[Y | X] = b(X)sign(w·X)`, `a ≤ b ≤ 1`). One verifier serves every marginal in `D_{τ_a}`: the
marginal is quantified inside `OMSoundOn`/`OMMassartCompleteOn`. The message type is
`ℝᵈ × (Fin N → FrameMsg d K_a)` with `N ≤ C log(e/ε)` frames; every output is the halfspace of the
message's unit candidate and every frame of an accepted message is orthonormal. `τ_a, K_a, C` depend
only on `a`; `0 < ε < 1`, `0 < δ ≤ 1/4` (standing ranges). -/
theorem theorem_G_1 (ηd : ℝ) (hd0 : 0 < ηd) (hd1 : ηd < 1 / 2) (hJ : Jeta ηd = 0) (a : ℝ)
    (ha : 1 - 2 * ηd < a) (ha1 : a < 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ (Ka : ℕ) (C : ℝ), ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ N : ℕ, (N : ℝ) ≤ C * Real.log (Real.exp 1 / ε) ∧
          ∃ (V : OneMsgVerifier d (Vec d × (Fin N → FrameMsg d Ka)))
            (Hon : HonestProver d (Vec d × (Fin N → FrameMsg d Ka))),
            ProperIn V ({halfRule} : Set (Vec 1 → Bool)) ∧
            (∀ (msg : Vec d × (Fin N → FrameMsg d Ka)) (s : Fin V.m → Vec d × Bool) (ω : V.Ω)
                (h : Vec d → Bool),
              V.decide msg s ω = some h →
                ‖msg.1‖ = 1 ∧ h = (fun x => sgn (inner ℝ msg.1 x)) ∧
                ∀ i : Fin N, (msg.2 i).2 ∈ stiefel d (msg.2 i).1) ∧
            OMSoundOn V (smoothFamily d τ) (halfspaceClass d) ε δ ∧
            OMMassartCompleteOn V Hon (smoothFamily d τ) (halfspaceClass d) ((1 - a) / 2) ε δ ∧
            (V.m : ℝ) ≤ C * (Real.sqrt d / ε * Real.log (Real.exp 1 / (ε * δ))) ∧
            (Hon.mP : ℝ) ≤ C * ((d * Real.log (Real.exp 1 / ε) +
              Real.log (Real.exp 1 / (ε * δ))) / ε ^ 2) := by sorry

end CondGeoVerif.Supplement
