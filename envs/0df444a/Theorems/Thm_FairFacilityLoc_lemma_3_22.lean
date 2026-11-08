-- Prove2me | Theorems.Thm_FairFacilityLoc_lemma_3_22
-- name    : FairFacilityLoc.lemma_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:46.637322+00:00
-- url     : https://prove2.me/theorems/8df2536d-a01a-42c9-97ac-95f21c34a4d6
-- title:
--   Lemma 3.22 — the threshold $\tau_d$ and the share bound
-- statement:
--   For $d\in\{1,2,3\}$ and $b=b_d$, the set of $t\in(0,1]$ with $2\gamma(t)\bar h(t)\ge\eta(t)$ is the interval $(0,\tau_d]$, where $\tau_1=1$, $\tau_2=1/\sqrt2$, $\tau_3=(25-\sqrt{157})/18$, and $\tau_d\ge1/\sqrt d$. If $\mathcal C>d$, every coordinate $r$ with $0<z_r\le\tau_d$ satisfies
--   $$s_r<\bar h(z_r)^2=g(z_r^2).$$
--
--   This bounds the shares of the coordinates with small entries of $z$.
--
--   **Scope of the hypothesis** $\mathcal C>d$ is the contradiction assumption of the proof of Proposition 3.17, which shows that it never holds for normalized data satisfying the capacity condition. This statement is a step of that proof, as on the page.
--
--   Differences from the source:
--   - generalization: normalized coordinates of a mechanism output, where Lemma 3.9 holds → any normalized family with $Q_r(a)\le K_r$ for all $a,r$ (CapacityCondition); reason: the proof uses the mechanism only through this inequality; Lemma 3.9 (`lemma_3_9`) supplies it for a mechanism output
--   - encoding: the normalization (3.2), with the output at the origin → the structure IsNormalized; reason: the fields are the hypotheses (3.2) for a finite nonnegative family with a vector of positive mass
--   - encoding: $d\le 3$ → $1\le d\le 3$; reason: dimensions are positive throughout the paper; (1.2) lists $1\le d\le3$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.22, p.41 (PDF p.43); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_hbar
import Definitions.Def_FairFacilityLoc_tau
import Definitions.Def_FairFacilityLoc_share
import Definitions.Def_FairFacilityLoc_IsNormalized

namespace FairFacilityLoc

/-- **Lemma 3.22** (Yan, Zhou, manuscript, sha256 642a1268…, p.41, PDF p.43). For `d ∈ {1, 2, 3}`, the set of
`t ∈ (0, 1]` with `2 γ(t) h̄(t) ≥ η(t)` is `(0, τ_d]`, and `τ_d ≥ 1/√d`. If `C > d`, every coordinate with
`0 < z_r ≤ τ_d` satisfies `s_r < h̄(z_r)² = g(z_r²)`.

**Formalization Note.** `b = b_d`. The second part is stated for weight families in normalized coordinates, as on
p.49; `CapacityCondition` is the conclusion of Lemma 3.9. -/
theorem lemma_3_22 (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        etaFun (penalty d) t ≤ 2 * gammaFun (penalty d) t * hbar d (penalty d) t} =
        Set.Ioc 0 (tau d) ∧
      1 / √(d : ℝ) ≤ tau d ∧
      ∀ {n : ℕ} {W : Finset (Fin n → ℝ)} {x : Fin n → GeoSemialgCSP.E d} {z : GeoSemialgCSP.E d},
        IsNormalized W x z → CapacityCondition (penalty d) W x →
        (d : ℝ) < weightedCapacity (penalty d) W x z →
        ∀ r, 0 < z r → z r ≤ tau d →
          share (penalty d) W x z r < hbar d (penalty d) (z r) ^ 2 ∧
            hbar d (penalty d) (z r) ^ 2 = gEnvelope d (penalty d) (z r ^ 2) := by sorry

end FairFacilityLoc
