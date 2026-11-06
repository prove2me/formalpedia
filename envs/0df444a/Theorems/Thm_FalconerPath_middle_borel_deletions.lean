-- Prove2me | Theorems.Thm_FalconerPath_middle_borel_deletions
-- name    : FalconerPath.middle_borel_deletions
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:49.169372+00:00
-- url     : https://prove2.me/theorems/359adccc-0427-4605-94a8-ccc5c2de51c6
-- title:
--   Two Borel deletions yielding a full-source radial threshold
-- statement:
--   Let $n\in\mathbb N$ and let $\nu,\rho$ be probabilities on $\mathbb R^n$. Let $G\subseteq\operatorname{supp}\nu\times\operatorname{supp}\rho$ be Borel. Fix $v\in\mathbb R^n$, $d\in\mathbb N$ and $r,f,\eta\in\mathbb R$ with $f,\eta\ge0$ and no sign condition on $r$. For $i\in\mathbb Z^n$, let $Q_i=\{z:v_\ell+i_\ell2^{-d}\le z_\ell<v_\ell+(i_\ell+1)2^{-d}\text{ for all }\ell\}$ and let $B_i^+\subseteq\mathbb R^n$ be Borel. Put $\pi_x(z)=\|z-x\|^{-1}(z-x)$ with value zero at $z=x$, $\lambda_z=(\pi_z)_\#(\nu|_{\{x:(x,z)\in G\}})$, $M_i(x,z)=\rho\{z'\in Q_i:\|\pi_x(z')-\pi_x(z)\|\le r\}$, and $\mathcal H_i(x)=\{z\in Q_i\cap\operatorname{supp}\rho:f\rho(Q_i)<M_i(x,z)\}$. Assume for every $i$ that for $\rho$-almost every $z$, $z\in Q_i$ implies $\lambda_z(B_i^+)\le\eta$. Also assume that for every $i$ with $\rho(Q_i)>0$ and every $x\in\operatorname{supp}\nu$, if there is $z\in Q_i\cap\operatorname{supp}\rho$ with $(x,z)\in G$ and $\pi_z(x)\notin B_i^+$, then $(\rho(Q_i)^{-1}\rho|_{Q_i})(\mathcal H_i(x))\le\eta$. There exists a Borel relation $H\subseteq G$ such that $(\nu\otimes\rho)(G\setminus H)\le2\eta$ and for every $(x,z)\in H$ and every $i$ with $z\in Q_i$, $M_i(x,z)\le f\rho(Q_i)$.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 5, Lemma 5.3 (prep:one-scale), the first Fubini deletion after (prep:witness-bad), together with the paragraph beginning with the pair relation surviving the bad-direction deletion. The latter integrates the heavy deletion over represented pins and sums with original source-cell weights, with zero cost for an unrepresented pin and a Borel threshold intersection requiring no measurable witness choice.

import Definitions.Def_FalconerPath_connect
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 5, Lemma 5.3, the two Fubini deletions: first delete pairs
whose reverse direction is in the cell's Borel bad set; then intersect with
the radial threshold event. Cell weights sum to one. A pin with no surviving
witness incurs zero second deletion. This elementary assembly statement is
valid for an arbitrary grid depth, radius and threshold; it assumes the
conditional heavy-set estimate and supplies no analytic gain of its own. -/
theorem middle_borel_deletions {n : ℕ}
    (ν ρ : Measure (Space n)) (hν : Probability ν) (hρ : Probability ρ)
    (G : PairSet n) (hG : MeasurableSet G) (hsupp : G ⊆ ν.support ×ˢ ρ.support)
    (v : Space n) (d : ℕ) (r f η : ℝ) (hf : 0 ≤ f) (hη : 0 ≤ η)
    (Bplus : (Fin n → ℤ) → Set (Space n))
    (hB : ∀ i, MeasurableSet (Bplus i))
    (hbad : ∀ i, ∀ᵐ z ∂ρ, z ∈ dyadicCell v d i →
      reverseDirection ν G z (Bplus i) ≤ ENNReal.ofReal η)
    (hheavy : ∀ i, 0 < ρ (dyadicCell v d i) → ∀ x ∈ ν.support,
      (∃ z ∈ dyadicCell v d i, z ∈ ρ.support ∧ (x,z) ∈ G ∧ radial z x ∉ Bplus i) →
      normalizedRestriction ρ (dyadicCell v d i)
        (connectHeavy ρ (dyadicCell v d i) r f x) ≤ ENNReal.ofReal η) :
    ∃ H : PairSet n, MeasurableSet H ∧ H ⊆ G ∧
      (ν.prod ρ) (G \ H) ≤ ENNReal.ofReal (2*η) ∧
      ∀ x z : Space n, (x,z) ∈ H → ∀ i : Fin n → ℤ,
        z ∈ dyadicCell v d i →
        connectRadialMass ρ (dyadicCell v d i) r x z ≤
          ENNReal.ofReal f * ρ (dyadicCell v d i) := by sorry
end FalconerPath
