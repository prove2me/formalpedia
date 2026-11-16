-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_F_1
-- name    : CondGeoVerif.Supplement.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:17:22.206373+00:00
-- url     : https://prove2.me/theorems/9c790d5e-b500-49d7-923f-5f646eec3f0e
-- title:
--   Theorem F.1 — centered slabs above $\eta>p(1-p)$: $m_V+\lceil512\log24/\Gamma^2\rceil>(d-1)/100$
-- statement:
--   Fix $t>0$, $p=2\Phi(t)-1$, centered slabs $S_{t,d}=\{x\mapsto2\cdot1\{|w\cdot x|\le t\}-1:w\in S^{d-1}\}$ and features $X\sim N(0,I_d)$. If $p(1-p)<\eta<1/2$, centered-slab verification requires $\Omega_{t,\eta,\varepsilon}(d)$ private observations at every fixed sufficiently small positive accuracy and confidence at least $2/3$, and completeness is needed only at the single known random-classification-noise anchor $\mathbb E[Y\mid X]=(1-2\eta)h_{e_1}(X)$. Explicitly, with
--   $$\Gamma=2\{p\min(\eta,1-p)+(1-p)\min(\eta,p)\}-2p(1-p)>0\qquad(F.1)$$
--   and every $d\ge2$, $0<\varepsilon\le\Gamma/8$, every verifier that is complete with probability at least $2/3$ at that anchor and sound with probability at least $2/3$ against all Gaussian-marginal labels (interaction and improper outputs allowed) satisfies
--   $$m_V+\Big\lceil\frac{512\log24}{\Gamma^2}\Big\rceil>\frac{d-1}{100}.$$
--
--   Differences from the source:
--   - reading: any verifier with arbitrary interaction and every prover strategy → the published IVerifier (finitely many rounds, measurable queries and outputs) and soundness against every measurable prover strategy; reason: same model as the live goal Theorem 3.1 and Theorem B.1; the paper's simulated honest prover is a measurable randomized strategy
--   - encoding: confidence at least 2/3 → complete and sound with probability 2/3 (δ = 1/3); reason: the weakest such hypothesis, as in the live goal
--   - encoding: the anchor E[Y | X] = (1 − 2η)h_{e₁}(X) → a law Q given by IsLabelLaw with base rule h_{e₁} and error probability η; reason: characterizes the anchor uniquely
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem F.1 and (F.1)–(F.2), p.47 (PDF p.50)

import Mathlib
import Definitions.Def_CondGeoVerif_IVerifier
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory Cohen2019.Robust

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem F.1** (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, p.47 = PDF p.50). Fix a slab width `t > 0`, `p = 2Φ(t) − 1`, and a
noise level `η < 1/2` with `η > p(1 − p)`. Write
`Γ = 2{p min(η, 1 − p) + (1 − p) min(η, p)} − 2p(1 − p) > 0` (F.1). For `d ≥ 2` and
`0 < ε ≤ Γ/8`, every verifier for centered slabs `S_{t,d}` that is complete with probability at
least `2/3` at the single known random-classification-noise anchor `E[Y | X] = (1 − 2η)h_{e₁}(X)`
and sound with probability at least `2/3` against all Gaussian-marginal labels satisfies
`m_V + ⌈512 log 24/Γ²⌉ > (d − 1)/100`. Interaction and improper outputs are allowed.

**Formalization Note** Verifiers are the published `IVerifier`s. The anchor `Q` is given by its
characterizing property `IsLabelLaw` (Gaussian marginal, `Y ≠ h_{e₁}(X)` with probability exactly
`η` independently of `X`), with `h_{e₁}` the slab of the first coordinate vector. Confidence `2/3`
is `δ = 1/3`. `⌈·⌉` is the natural-number ceiling, `log` the natural logarithm. -/
theorem theorem_F_1 {t η : ℝ} (ht : 0 < t) (hη1 : η < 1 / 2)
    (hη : (2 * Phi t - 1) * (1 - (2 * Phi t - 1)) < η) {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε)
    (hε : ε ≤ (2 * ((2 * Phi t - 1) * min η (1 - (2 * Phi t - 1)) +
        (1 - (2 * Phi t - 1)) * min η (2 * Phi t - 1)) -
        2 * (2 * Phi t - 1) * (1 - (2 * Phi t - 1))) / 8)
    (V : IVerifier d) (Q : ProbabilityMeasure (Vec d × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule (slabRule t) (coordFrame d 1))
      (fun _ => η))
    (hcomp : ICompleteAt V Q (slabClass t d) ε (1 / 3)) (hsound : ISound V (slabClass t d) ε (1 / 3)) :
    ((d : ℝ) - 1) / 100 < (V.m : ℝ) +
      ⌈512 * Real.log 24 / (2 * ((2 * Phi t - 1) * min η (1 - (2 * Phi t - 1)) +
        (1 - (2 * Phi t - 1)) * min η (2 * Phi t - 1)) -
        2 * (2 * Phi t - 1) * (1 - (2 * Phi t - 1))) ^ 2⌉₊ := by sorry

end CondGeoVerif.Supplement
