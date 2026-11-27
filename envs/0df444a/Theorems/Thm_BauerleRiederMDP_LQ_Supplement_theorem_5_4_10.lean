-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_5_4_10
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_5_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:55:34.42027+00:00
-- url     : https://prove2.me/theorems/6a59c0b7-8950-5406-aa9f-df261094687f
-- title:
--   Theorem 5.4.10 (corrected: explicit Bayes rule of Φ̂) — Bayesian models: increasing functions satisfy (SA_N)
-- statement:
--   Suppose an information-based Markov Decision Model with an upper bounding function $b$ is given and (i) $D(\cdot )$ is increasing, i.e. $x \le  x'$ implies $D(x) \subset  D(x')$, (ii) $q^Z(\cdot |\theta , a) \le _lr q^Z(\cdot |\theta ', a)$ for all $\theta  \le  \theta '$ and $a \in  A$, (iii) $(x, z) \mapsto  T_X(x, a, z)$ is increasing for all $a \in  D(x)$, (iv) $(\theta , x) \mapsto  r(\theta , x, a)$ is increasing for all $a \in  D(x)$, (v) $(\theta , x) \mapsto  g(\theta , x)$ is increasing, (vi) for all increasing $v \in  IB_b^+$ there exists a maximizer $f \in  \Delta $ of $v$. Then the sets `IM := {v ∈ IB_b^+ | v is increasing}` and $\Delta $ satisfy the Structure Assumption (SA_N).
--
--   **Formalization Note.** The assumptions of p.164: $\mathcal Z  \subset  \mathbb R $, $E_X \subset  \mathbb R ^d$, $\Theta  \subset  \mathbb R $ (Borel subsets, as subtypes with the componentwise order); $Q^Z(\cdot |x, \theta , a)$ independent of $x$ with density $q^Z(\cdot |\theta , a)$ w.r.t. a σ-finite measure; $\hat{\mu}$ has a $Q_0$-density $\hat{p}(\theta |i)$. The order on $E_X \times  I$ is the componentwise order on $E_X$ and $i \le  i' :⇔ \hat{\mu}(\cdot |i) \le _lr \hat{\mu}(\cdot |i')$, i.e. $\hat{p}(\theta '|i) \hat{p}(\theta |i') \le  \hat{p}(\theta |i) \hat{p}(\theta '|i')$ for $\theta  \le  \theta '$ (Definition B.3.5, a preorder); $\le _lr$ in (ii) is the same product form for the densities $q^Z$. **The correction:** the book's proof identifies $\hat{\mu}(\cdot |\hat{\Phi}(i, a, z))$ with the Bayes update of $\hat{\mu}(\cdot |i)$, which Definition 5.4.5 gives only at information states $t_n(\tilde{h}_n)$; it is assumed here for every $i$ and predictive-almost every $z$ ($\hat{\Phi}$ is not required to be anything at $z$ of zero likelihood, where the posterior is arbitrary). The upper bounding function is Definition 2.4.1 for the information-based model. $\Delta $ is a set of decision rules (p.23). (SA_N) is `SeqSuffStat.StructureAssumption` with the constant families $IM$, $\Delta $; the Integrability Assumption of p.151 is in force.
--
--   Differences from the source:
--   - correction: Φ̂ the update of a sequential sufficient statistic → Φ̂(i,z) is the Bayes update of μ̂(·|i) for every i and predictive-a.e. z; reason: the proof uses the Bayes identity at every information state, which Definition 5.4.5 gives only at reachable states t_n(h̃_n); without it the monotonicity can fail at unreachable states
--   - encoding: μ̂(·|i) ≤_lr μ̂(·|i′) → product inequality of the Q_0-densities p̂; reason: Definition B.3.5 with the dominating measure Q_0
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 5.4.10, p.165 (PDF 178)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_law
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_Jpi
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_J
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_rhat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_ghat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_QhatZ
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Lhat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_That
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoState
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoLaw
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhatpi
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_IsMaximizer
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_StructureAssumption
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory
open MDPFinance.Contracting (IBbPlus)
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 5.4.10** (Bayes rule of `Φ̂` made explicit) (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Theorem 5.4.10, p.165, PDF 178, under the assumptions of
"Monotonicity Results", p.164, PDF 177). Suppose an information-based Markov Decision Model with an
upper bounding function `b` is given and
(i) `D(·)` is increasing, i.e. `x ≤ x′` implies `D(x) ⊂ D(x′)`,
(ii) `q^Z(·|θ, a) ≤_lr q^Z(·|θ′, a)` for all `θ ≤ θ′` and `a ∈ A`,
(iii) `(x, z) ↦ T_X(x, a, z)` is increasing for all `a ∈ D(x)`,
(iv) `(θ, x) ↦ r(θ, x, a)` is increasing for all `a ∈ D(x)`,
(v) `(θ, x) ↦ g(θ, x)` is increasing,
(vi) for all increasing `v ∈ IB_b^+` there exists a maximizer `f ∈ Δ` of `v`.
Then the sets `IM := {v ∈ IB_b^+ | v is increasing}` and `Δ` satisfy the Structure Assumption (SA_N).

**Formalization Note.** The assumptions of p.164: `𝒵 ⊂ ℝ`, `E_X ⊂ ℝ^d`, `Θ ⊂ ℝ` (Borel subsets, as
subtypes with the componentwise order); `Q^Z(·|x, θ, a)` independent of `x` with density `q^Z(·|θ, a)`
w.r.t. a σ-finite measure; `μ̂` has a `Q_0`-density `p̂(θ|i)`. The order on `E_X × I` is the
componentwise order on `E_X` and `i ≤ i′ :⇔ μ̂(·|i) ≤_lr μ̂(·|i′)`, i.e. `p̂(θ′|i) p̂(θ|i′) ≤ p̂(θ|i) p̂(θ′|i′)`
for `θ ≤ θ′` (Definition B.3.5, a preorder); `≤_lr` in (ii) is the same product form for the densities
`q^Z`. **The correction:** the book's proof identifies `μ̂(·|Φ̂(i, a, z))` with the Bayes update of
`μ̂(·|i)`, which Definition 5.4.5 gives only at information states `t_n(h̃_n)`; it is assumed here for
every `i` and predictive-almost every `z` (`Φ̂` is not required to be anything at `z` of zero
likelihood, where the posterior is arbitrary). The upper bounding function is Definition 2.4.1 for the
information-based model. `Δ` is a set of decision rules (p.23). (SA_N) is `SeqSuffStat.StructureAssumption`
with the constant families `IM`, `Δ`; the Integrability Assumption of p.151 is in force. -/
theorem theorem_5_4_10 {d : ℕ} {SX : Set (Fin d → ℝ)} {SZ SΘ : Set ℝ}
    (hSX : MeasurableSet SX) (hSZ : MeasurableSet SZ) (hSΘ : MeasurableSet SΘ)
    {A : Type} [MeasurableSpace A] [StandardBorelSpace A] {I : Type*} [MeasurableSpace I]
    (M : BayesModel SX A SZ SΘ) (S : SeqSuffStat M I) (N : ℕ)
    (hInt : M.IntegrabilityAssumption N)
    (hqx : ∀ (x x' : SX) θ a z, M.qZ (x, θ, a) z = M.qZ (x', θ, a) z)
    (phat : I → SΘ → ℝ≥0∞) (hphat_meas : Measurable (Function.uncurry phat))
    (hphat : ∀ i, S.muhat i = M.Q0.withDensity (phat i))
    (hbayes : ∀ (x : SX) (i : I) (a : A), ∀ᵐ z ∂(S.QhatZ x i a),
      S.muhat (S.Phihat (x, i, a, z)) =
        (∫⁻ θ, M.qZ (x, θ, a) z ∂(S.muhat i))⁻¹ • (S.muhat i).withDensity fun θ => M.qZ (x, θ, a) z)
    (b : SX × I → ℝ)
    (hb : Measurable b ∧ (∀ p, 0 ≤ b p) ∧ ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ x i a, (x, a) ∈ M.D → S.rhat x i a ⊔ 0 ≤ ((cr * b (x, i) : ℝ) : EReal)) ∧
      (∀ x i, S.ghat x i ⊔ 0 ≤ ((cg * b (x, i) : ℝ) : EReal)) ∧
      ∀ x i a, (x, a) ∈ M.D →
        ∫⁻ z, ENNReal.ofReal (b (M.TX (x, a, z), S.Phihat (x, i, a, z))) ∂(S.QhatZ x i a) ≤
          ENNReal.ofReal (αb * b (x, i)))
    (Δ : Set (SX × I → A)) (hΔ : ∀ f ∈ Δ, Measurable f ∧ ∀ p : SX × I, (p.1, f p) ∈ M.D)
    (hD : ∀ x x' : SX, x ≤ x' → ∀ a, (x, a) ∈ M.D → (x', a) ∈ M.D)
    (hlr : ∀ (θ θ' : SΘ), θ ≤ θ' → ∀ (x : SX) (a : A) (z z' : SZ), z ≤ z' →
      M.qZ (x, θ, a) z' * M.qZ (x, θ', a) z ≤ M.qZ (x, θ, a) z * M.qZ (x, θ', a) z')
    (hT : ∀ (x x' : SX) (z z' : SZ) (a : A), x ≤ x' → z ≤ z' → (x, a) ∈ M.D →
      M.TX (x, a, z) ≤ M.TX (x', a, z'))
    (hr : ∀ (θ θ' : SΘ) (x x' : SX) (a : A), θ ≤ θ' → x ≤ x' → (x, a) ∈ M.D →
      M.r (x, θ, a) ≤ M.r (x', θ', a))
    (hg : ∀ (θ θ' : SΘ) (x x' : SX), θ ≤ θ' → x ≤ x' → M.g (x, θ) ≤ M.g (x', θ'))
    (hmax : ∀ v ∈ IBbPlus b,
      (∀ (x x' : SX) (i i' : I), x ≤ x' →
        (∀ θ θ' : SΘ, θ ≤ θ' → phat i θ' * phat i' θ ≤ phat i θ * phat i' θ') →
          v (x, i) ≤ v (x', i')) →
      ∃ f ∈ Δ, S.IsMaximizer v f) :
    S.StructureAssumption N
      (fun _ => {v | v ∈ IBbPlus b ∧ ∀ (x x' : SX) (i i' : I), x ≤ x' →
        (∀ θ θ' : SΘ, θ ≤ θ' → phat i θ' * phat i' θ ≤ phat i θ * phat i' θ') →
          v (x, i) ≤ v (x', i')})
      (fun _ => Δ) := by sorry

end BauerleRiederMDP.LQ.Supplement
