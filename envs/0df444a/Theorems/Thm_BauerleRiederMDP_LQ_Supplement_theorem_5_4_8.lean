-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_5_4_8
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_5_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:54:40.808918+00:00
-- url     : https://prove2.me/theorems/06f3de90-df7c-5d40-a3dc-135b43bb69f7
-- title:
--   Theorem 5.4.8 — Bellman equation of the information-based model; maximizers give an optimal Bayesian policy
-- statement:
--   Suppose the information-based Markov Decision Model satisfies the Structure Assumption of Theorem 2.3.8. a) Then the Bellman equation holds, i.e. for $(x, i) \in  E_X \times  I$: $\hat J _0(x, i) = \int  g(x, \theta ) \hat{\mu}(d\theta |i)$, $\hat J _n(x, i) = \sup _{a \in  D(x)} {\int  r(x, \theta , a) \hat{\mu}(d\theta |i) + \beta  \int \int  \hat J _{n-1}(T_X(x, a, z), \hat{\Phi}(x, i, a, z)) Q^Z(dz|x, \theta , a) \hat{\mu}(d\theta |i)}$. b) Let $\hat{f}_n$ be a maximizer of $\hat J _{n-1}$ for $n = 1, \dots , N$. Then the policy $\pi ^* := (f^*_0, \dots , f^*_{N-1})$ is optimal for the $N$-stage Bayesian Model, where $f^*_n(\tilde{h}_n) := \hat{f}_{N-n}(x_n, t_n(\tilde{h}_n))$, $\tilde{h}_n \in  \tilde{H}_n$.
--
--   **Formalization Note.** The hypothesis is the stage-indexed (SA_N) of p.23 for the information-based model (`SeqSuffStat.StructureAssumption`, time running forwards, $IM_n$ and $\Delta _n$ depending on the stage), as for the published Theorem 5.3.3; the Integrability Assumption of p.151 is in force. $\hat J _n$ is the $n$-stage value (a supremum over $\tilde{\Pi}_n$), indexed by stages to go; a) is stated for $n = 1, \dots , N$. The operator $\hat{T}$ integrates against $\hat{Q}^Z(\cdot |x, i, a) = \int  Q^Z(\cdot |x, \theta , a) \hat{\mu}(d\theta |i)$, which is the iterated integral of the display. Optimality means $J_{N\pi ^*}(x) = J_N(x)$ for all $x$.
--
--   Differences from the source:
--   - encoding: Structure Assumption of Theorem 2.3.8 → the stage-indexed (SA_N) for the information-based model (SeqSuffStat.StructureAssumption); reason: the book's assumption written for this model; same content
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 5.4.8, p.163 (PDF 176)

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

/-- **Theorem 5.4.8** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 5.4.8, p.163, PDF 176). Suppose the information-based Markov Decision Model satisfies
the Structure Assumption of Theorem 2.3.8.
a) Then the Bellman equation holds, i.e. for `(x, i) ∈ E_X × I`: `Ĵ_0(x, i) = ∫ g(x, θ) μ̂(dθ|i)`,
`Ĵ_n(x, i) = sup_{a ∈ D(x)} {∫ r(x, θ, a) μ̂(dθ|i) + β ∫∫ Ĵ_{n−1}(T_X(x, a, z), Φ̂(x, i, a, z)) Q^Z(dz|x, θ, a) μ̂(dθ|i)}`.
b) Let `f̂_n` be a maximizer of `Ĵ_{n−1}` for `n = 1, …, N`. Then the policy `π* := (f*_0, …, f*_{N−1})` is
optimal for the `N`-stage Bayesian Model, where `f*_n(h̃_n) := f̂_{N−n}(x_n, t_n(h̃_n))`, `h̃_n ∈ H̃_n`.

**Formalization Note.** The hypothesis is the stage-indexed (SA_N) of p.23 for the information-based
model (`SeqSuffStat.StructureAssumption`, time running forwards, `IM_n` and `Δ_n` depending on the
stage), as for the published Theorem 5.3.3; the Integrability Assumption of p.151 is in force.
`Ĵ_n` is the `n`-stage value (a supremum over `Π̃_n`), indexed by stages to go; a) is stated for
`n = 1, …, N`. The operator `T̂` integrates against `Q̂^Z(·|x, i, a) = ∫ Q^Z(·|x, θ, a) μ̂(dθ|i)`, which is
the iterated integral of the display. Optimality means `J_{Nπ*}(x) = J_N(x)` for all `x`. -/
theorem theorem_5_4_8 {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] [StandardBorelSpace EX]
    [StandardBorelSpace A] [StandardBorelSpace Z] [StandardBorelSpace Θ]
    (M : BayesModel EX A Z Θ) (S : SeqSuffStat M I) (N : ℕ)
    (hInt : M.IntegrabilityAssumption N)
    (IMs : ℕ → Set (EX × I → EReal)) (Deltas : ℕ → Set (EX × I → A))
    (hSA : S.StructureAssumption N IMs Deltas) :
    (∀ (x : EX) (i : I), S.Jhat 0 x i = S.ghat x i) ∧
    (∀ n, 1 ≤ n → n ≤ N → ∀ (x : EX) (i : I),
      S.Jhat n x i = S.That (fun p => S.Jhat (n - 1) p.1 p.2) (x, i)) ∧
    ∀ fhat : ℕ → EX × I → A,
      (∀ n, 1 ≤ n → n ≤ N → S.IsMaximizer (fun p => S.Jhat (n - 1) p.1 p.2) (fhat n)) →
      M.IsPolicy N (fun k h => fhat (N - k) (Htil.state k h, S.t k h)) ∧
        ∀ x : EX, M.Jpi N (fun k h => fhat (N - k) (Htil.state k h, S.t k h)) x = M.J N x := by sorry

end BauerleRiederMDP.LQ.Supplement
