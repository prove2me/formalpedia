-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_5_4_7
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_5_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:53:41.892921+00:00
-- url     : https://prove2.me/theorems/481ff1ac-01e8-509b-8dd8-b9075266d5cb
-- title:
--   Theorem 5.4.7 — the information-based model has the same value as the Bayesian problem
-- statement:
--   Suppose a Bayesian Model with a sequential sufficient statistic $(t_n)$ is given and $\pi  \in  \tilde{\Pi}_N$. Then for $x \in  E_X$: $J_{N\pi }(x) = \hat J _{N\pi }(x, t_0)$ and $J_N(x) = \hat J _N(x, t_0)$.
--
--   **Formalization Note.** $E_X$, $A$, $\mathcal Z $, $\Theta $ are standard Borel (Chapter 5, p.148); the information space $I$ is an arbitrary measurable space (Definition 5.4.3). The Integrability Assumption of p.151 is in force. $J_{N\pi }$, $J_N$ are the Bayesian expected reward and its supremum over $\tilde{\Pi}_N$; $\hat J _{N\pi }$, $\hat J _N$ those of the information-based model (Definition 5.4.6), both over the history-dependent policies $\tilde{\Pi}_N$ with rules on $\tilde{H}_k$ (p.163). $t_0$ is $t_0(x)$ ($t_0(x_0) ≡ t_0$, p.161).
--
--   Differences from the source:
--   - encoding: E_X, A, Z, Θ Borel spaces → standard Borel spaces; I an arbitrary measurable space; reason: Lean encoding of Chapter 5's standing assumption
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 5.4.7, p.163 (PDF 176)

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

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **Theorem 5.4.7** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 5.4.7, p.163, PDF 176). Suppose a Bayesian Model with a sequential sufficient
statistic `(t_n)` is given and `π ∈ Π̃_N`. Then for `x ∈ E_X`:
`J_{Nπ}(x) = Ĵ_{Nπ}(x, t_0)` and `J_N(x) = Ĵ_N(x, t_0)`.

**Formalization Note.** `E_X`, `A`, `𝒵`, `Θ` are standard Borel (Chapter 5, p.148); the information
space `I` is an arbitrary measurable space (Definition 5.4.3). The Integrability Assumption of p.151
is in force. `J_{Nπ}`, `J_N` are the Bayesian expected reward and its supremum over `Π̃_N`; `Ĵ_{Nπ}`,
`Ĵ_N` those of the information-based model (Definition 5.4.6), both over the history-dependent
policies `Π̃_N` with rules on `H̃_k` (p.163). `t_0` is `t_0(x)` (`t_0(x_0) ≡ t_0`, p.161). -/
theorem theorem_5_4_7 {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] [StandardBorelSpace EX]
    [StandardBorelSpace A] [StandardBorelSpace Z] [StandardBorelSpace Θ]
    (M : BayesModel EX A Z Θ) (S : SeqSuffStat M I) (N : ℕ)
    (hInt : M.IntegrabilityAssumption N) :
    (∀ π : (k : ℕ) → Htil EX A Z k → A, M.IsPolicy N π →
      ∀ x : EX, M.Jpi N π x = S.Jhatpi N π x (S.t 0 x)) ∧
    ∀ x : EX, M.J N x = S.Jhat N x (S.t 0 x) := by sorry

end BauerleRiederMDP.LQ.Supplement
