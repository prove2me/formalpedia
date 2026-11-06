-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_19
-- name    : AdvMultiplayer.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:15:44.646602+00:00
-- url     : https://prove2.me/theorems/9397483b-ca89-44ec-8952-028f19ba1ad8
-- title:
--   Lemma 19 — exact simulation and deferred assignment law
-- statement:
--   Run the fresh-row reference physical protocol and Algorithm 1 with the same launch and episode schedule, starting with zero scores and queues. There are a probability space carrying both executions and a filtration $(\mathcal F_r)$ of joint pre-round histories such that: (i) the physical execution has its prescribed law; (ii) the logical execution is a realization of Algorithm 1 satisfying (I1)-(I4) with respect to $(\mathcal F_r)$; (iii) almost surely $\tau_*^{\mathrm{phys}}=\tau_*$, $(Z(r),\mathsf B_r)=(\hat z(r),\hat{\mathsf B}_r)$ from launch for $r\le\min\{\tau_*,T\}+1$, on live rounds $r\le\tau_*$ the assigned physical slow set is $\hat U_r$, and every physical fast-arm draw is the logical fast arm; (iv) at every assignment start $t\le\tau_*^{\mathrm{phys}}$ and for every $(m-1)$-set $U$,
--   $$\Pr(\hat U_t=U\mid\mathcal G_t^-)=\Pr(\hat U_t=U\mid\mathcal G_t^+)=\bar\nu_t(U).$$
--   This is the bridge between the local protocol and the learner of Section 3.
--
--   Differences from the source:
--   - encoding: a filtration of joint pre-round histories → a filtration containing the physical pre-round history; reason: this is what “joint” means on p.37; the physical history is pulled back along the map to the fresh-row space
--   - encoding: row coordinates inspected before the sampler → `inspectedScalar`, `inspectedFwd` and the selected affine map; reason: the read set of the protocol, written as a mask
--   - encoding: rewards rounded down to multiples of 1/D (Section 3 onward, p.6) → `IsRounded`; reason: standing convention of the section; the same matrices
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 19, p.36, (39)

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 19 (exact simulation and deferred assignment law).** Gan, arXiv:2610.05688, Lemma 19, p.36.
Run the fresh-row reference physical protocol and Algorithm 1 with the same launch and episode schedule.
There are a probability space carrying both executions and a filtration `(ℱ_r)` of joint pre-round
histories with (i)–(iv).

**Formalization Note.** `phys` is the physical execution's randomness on the joint space, so (i) says
the joint law's physical marginal is the fresh-row law, including unread row coordinates. `ℱ_r` contains
the physical pre-round history. The learner's `isStart` is the physical schedule. (iii) and (iv) are
stated a.s. and on each assignment start `t`; `G_t^±` are `Gminus`, `Gplus` pulled back by `phys`. -/
theorem lemma_19 (p : Size) (hb : p.branch) (idA : IdArray p) (r : Rewards p) (hr : IsRounded p r) :
    ∃ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (phys : Ω → FreshΩ p) (L : Learner p Ω)
      (Hpre Hupd Hprop : ℕ → MeasurableSpace Ω),
      -- (i)
      Measurable phys ∧ μ.map phys = freshLaw p ∧
      (∀ t, MeasurableSpace.comap phys ((preRound p) t) ≤ ℱ t) ∧
      -- (ii)
      L.IsRealization p.eta μ ℱ r Hpre Hupd Hprop ∧
      (∀ t ω, L.isStart t ω ↔ episodeStartAt p (freshTrace p idA r (phys ω)) t) ∧
      -- (iii)
      (∀ᵐ ω ∂μ,
        tauPhys p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) = L.tauStar p.eta ω ∧
        (∀ t, launchRound p (freshTrace p idA r (phys ω)) ≤ t →
          ((t : ℕ∞) ≤ min (L.tauStar p.eta ω) (p.T : ℕ∞) + 1) → ∀ j,
          calScore p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) t j = L.z t ω j ∧
          calQueue p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) t j = L.Bq t ω j) ∧
        (∀ t ∈ Finset.Icc 1 p.T, (t : ℕ∞) ≤ L.tauStar p.eta ω →
          liveAt p (freshTrace p idA r (phys ω)) t →
          slowSetAt p (freshTrace p idA r (phys ω)) t = L.slow t ω ∧
          ((coAt p (freshTrace p idA r (phys ω)) t).co.fastNow = true →
            (freshTrace p idA r (phys ω) t).arms (coordinator p) = L.fast t ω))) ∧
      -- (iv)
      ∀ t ∈ Finset.Icc 1 p.T, ∀ U ∈ Finset.powersetCard (p.m - 1) (Finset.univ : Finset (Fin p.K)),
        ∀ᵐ ω ∂μ, assignStartAt p (freshTrace p idA r (phys ω)) t →
          (t : ℕ∞) ≤ tauPhys p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) →
          (μ[Learner.ind {ω | L.slow t ω = U} |
              MeasurableSpace.comap phys (Gminus p idA r t)]) ω =
            nuBar p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) t U ∧
          (μ[Learner.ind {ω | L.slow t ω = U} | MeasurableSpace.comap phys (Gplus p t)]) ω =
            nuBar p (idA, (phys ω).1) (freshTrace p idA r (phys ω)) t U := by sorry

end AdvMultiplayer
