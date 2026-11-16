-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_C_1
-- name    : CondGeoVerif.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:12:57.704743+00:00
-- url     : https://prove2.me/theorems/f7dd4b5e-cfda-455d-b2bb-c02fc096858d
-- title:
--   Theorem C.1 — a fixed essential Boolean composition of orthogonal halfspaces has an $O_b(\varepsilon^{-1}\log(e/(\varepsilon\delta)))$ proper one-message verifier
-- statement:
--   Fix an essential Boolean function $b:\{-1,1\}^k\to\{-1,1\}$ (each coordinate is pivotal for some assignment of the others), put $f(u)=b(\mathrm{sign}\,u_1,\dots,\mathrm{sign}\,u_k)$ and $\mathcal H_{b,d}=\{x\mapsto f(W^\top x):W^\top W=I_k\}$, with features $X\sim N(0,I_d)$.
--
--   There is $\eta_b>0$ such that, for every $d\ge k$, $0<\varepsilon<1$ and $0<\delta\le1/4$, there is a proper one-message verifier with Massart completeness at noise bound $\eta_b$ and arbitrary-label Gaussian soundness using
--   $$m_V=O_b\Big(\frac1\varepsilon\log\frac e{\varepsilon\delta}\Big),\qquad m_P=O_b\Big(\frac{d\log(e/\varepsilon)+\log(1/\delta)}{\varepsilon^2}\Big).$$
--
--   The message contains just a proposed orthonormal $k$-frame. In particular the conclusion holds at every smaller Massart noise bound. The theorem includes parity, conjunction and majority of any fixed number of orthogonal homogeneous halfspaces; Theorem C.7 makes the rank dependence explicit.
--
--   Differences from the source:
--   - encoding: O_b(·) → one constant C chosen after b and η_b, before d, ε, δ; reason: the subscript names the only dependence
--   - reading: there is η_b > 0 (a Massart noise bound) → 0 < η_b < 1/2; reason: Massart noise bounds lie in [0, 1/2) throughout the paper ((2.1), p.3); the proof takes η_b ≤ 1/4
--   - encoding: the message contains just a proposed orthonormal k-frame → message type ℝ^{d×k}; every output is x ↦ b(sign(Wᵀx)) for the message W, which is then orthonormal (malformed frames rejected); reason: the proof outputs the candidate frame's predictor and rejects malformed frames (§C.3, p.32); "every smaller noise bound" follows because Massart noise at η ≤ η_b is Massart noise at η_b
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem C.1, p.28 (PDF p.31); proof §C.2–C.3, pp.31–32

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem C.1** (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, p.28 = PDF p.31). For every fixed essential Boolean rule
`b : {−1, 1}ᵏ → {−1, 1}` there is `η_b > 0` such that, for every `d ≥ k`, `0 < ε < 1` and
`0 < δ ≤ 1/4`, the class `H_{b,d} = {x ↦ b(sign(Wᵀx)) : WᵀW = I_k}` has a proper one-message
verifier with Massart completeness at noise bound `η_b` and arbitrary-label Gaussian soundness using
`m_V = O_b(ε⁻¹ log(e/(εδ)))` private samples and an honest prover with
`m_P = O_b((d log(e/ε) + log(1/δ))/ε²)` samples. The message contains just a proposed orthonormal
`k`-frame. In particular the conclusion holds at every smaller Massart noise bound.

**Formalization Note** `O_b` is a constant `C` chosen after `b` (and `η_b`) and before `d, ε, δ`.
`η_b < 1/2` is the standing range of Massart noise. Properness is `ProperIn` with the single rule
`boolComp b`. The message type is `ℝ^{d×k}` (a proposed frame `W`); whenever the verifier outputs
`h`, the message `W` is orthonormal and `h = x ↦ b(sign(Wᵀx))` (malformed frames are rejected).
The "every smaller Massart noise bound" clause follows from the statement, since Massart noise at a
bound `η ≤ η_b` is Massart noise at `η_b`. -/
theorem theorem_C_1 {k : ℕ} (b : (Fin k → Bool) → Bool) (hb : IsEssential b) :
    ∃ ηb : ℝ, 0 < ηb ∧ ηb < 1 / 2 ∧ ∃ C : ℝ, ∀ d : ℕ, k ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ (V : OneMsgVerifier d (Matrix (Fin d) (Fin k) ℝ))
          (Hon : HonestProver d (Matrix (Fin d) (Fin k) ℝ)),
          ProperIn V ({boolComp b} : Set (Vec k → Bool)) ∧
          (∀ (W : Matrix (Fin d) (Fin k) ℝ) (s : Fin V.m → Vec d × Bool) (ω : V.Ω)
              (h : Vec d → Bool),
            V.decide W s ω = some h → W ∈ stiefel d k ∧ h = frameRule (boolComp b) W) ∧
          OMSound V (projClass {boolComp b} d) ε δ ∧
          OMMassartComplete V Hon (projClass {boolComp b} d) ηb ε δ ∧
          (V.m : ℝ) ≤ C * (1 / ε) * Real.log (Real.exp 1 / (ε * δ)) ∧
          (Hon.mP : ℝ) ≤ C * ((d * Real.log (Real.exp 1 / ε) + Real.log (1 / δ)) / ε ^ 2) := by sorry

end CondGeoVerif.Supplement
