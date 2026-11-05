-- Prove2me | Theorems.Thm_BauerleRiederMDP_Contracting_theorem_7_3_6
-- name    : BauerleRiederMDP.Contracting.theorem_7_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:48.897396+00:00
-- url     : https://prove2.me/theorems/781d04d3-129f-4e3a-8cbb-5b9599a47815
-- title:
--   Theorem 7.3.6 — continuous contracting models; value iteration, unique continuous fixed point, policy iteration and an optimal stationary policy
-- statement:
--   Let $E$ and $A$ be Borel spaces and $D$ a Borel subset of $E\times A$, and consider a stationary Markov Decision Model $(E,A,D,Q,r,\beta)$ with a **continuous** bounding function $b$ (constants $c_r,\alpha_b$) such that $\beta\alpha_b<1$. Assume:
--
--   1. $D(x)$ is compact for all $x\in E$ and $x\mapsto D(x)$ is continuous (upper and lower semicontinuous in the sense of Definition A.2.1);
--   2. $(x,a)\mapsto\int v(x')\,Q(dx'\mid x,a)$ is continuous for every continuous $v\in\mathbb B_b$;
--   3. $(x,a)\mapsto r(x,a)$ is continuous.
--
--   For $n\in\mathbb N\cup\{\infty\}$ let $D^*_n(x)$ be the set of maximum points of $a\mapsto LJ_{n-1}(x,a)$ on $D(x)$, where $Lv(x,a)=r(x,a)+\beta\int v\,dQ(\cdot\mid x,a)$, $J_n$ is the $n$-stage value and $J_{\infty-1}:=J_\infty$. Let $\mathrm{Ls}\,D^*_n(x)$ be the set of accumulation points of sequences $(a_n)$ with $a_n\in D^*_n(x)$ for $n\in\mathbb N$. Then:
--
--   1. $J_\infty$ is continuous, $J_\infty\in\mathbb B_b$, and $J_\infty=J=\lim_n J_n$ (**value iteration**);
--   2. $J_\infty$ is the unique continuous fixed point of $\mathcal T$ in $\mathbb B_b$;
--   3. $\emptyset\neq\mathrm{Ls}\,D^*_n(x)\subset D^*_\infty(x)$ for all $x\in E$ (**policy iteration**);
--   4. there is a decision rule $f^*\in F$ with $f^*(x)\in\mathrm{Ls}\,D^*_n(x)$ for all $x\in E$, and the stationary policy $(f^*,f^*,\dots)$ is optimal.
--
--   This is the continuous specialization of the Structure Theorem 7.3.5, with the set $\mathbb M$ of continuous functions in $\mathbb B_b$. It also gives policy iteration: limits of finite-horizon optimal actions are optimal for the infinite horizon.
--
--   **Formalization Note** A Borel space is encoded as a metrizable, second-countable space whose Borel σ-algebra is standard Borel. The model, $\mathbb B_b$, $\mathcal T$, $L$, $J_n$, $J_\infty$, the maximum-point sets, $\mathrm{Ls}$ and continuity of $x\mapsto D(x)$ are the published `MDPFinance.Contracting` bundles. The sequence $D^*_{n+1}$, $n\ge0$, is used, which has the same accumulation points.
--
--   Differences from the source:
--   - encoding: Q a stochastic kernel from D to E and r : D → ℝ → Q a Markov kernel on E × A and r measurable on E × A; reason: only values on D enter any statement, and every kernel and reward on D extend to E × A.
--   - encoding: Borel spaces E, A (Borel subsets of Polish spaces) → metrizable, second-countable, standard Borel spaces with their Borel σ-algebras; reason: the two classes coincide (Lusin–Souslin).
--   - encoding: continuity of (x,a) ↦ ∫v dQ and of r on the domain D of Q and r → ContinuousOn D; reason: Q and r are only given on D.
--   - encoding: J_{∞π} = 𝔼^π_x[Σ_k β^k r(X_k, f_k(X_k))] → limsup_n J_{nπ}; reason: J_{∞π} = lim_n J_{nπ} under (C) (p.197, Theorem B.1.1), and (C) holds for contracting models (Remark 7.3.2 b)).
--   - encoding: J_∞ = J with J := lim_n J_n → J_n(x) → J_∞(x) in EReal for every x; reason: J is defined as this limit.
--   - encoding: J_∞ continuous and in IB_b → J_∞ real-valued, and its real version continuous and in IB_b; reason: J_∞ is [−∞,∞]-valued by definition.
--   - encoding: D*_n, n ∈ ℕ (maximizers of LJ_{n−1}) → the sequence n ↦ D*_{n+1} (maximizers of LJ_n), n ≥ 0; reason: an index shift does not change the accumulation points.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Theorem 7.3.6, p.208 (PDF p.219); D*_n and Ls D*_n, p.201 (PDF p.212); Definition A.2.1, p.351 (PDF p.357)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

/-- **Theorem 7.3.6** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 7.3.6, p.208, PDF p.219). `E` and `A` are Borel spaces and `D` is a Borel subset
of `E × A`. Let `b` be a continuous bounding function and `β α_b < 1`. If
(i) `D(x)` is compact for all `x ∈ E` and `x ↦ D(x)` is continuous,
(ii) `(x,a) ↦ ∫ v(x') Q(dx'|x,a)` is continuous for all continuous `v ∈ IB_b`,
(iii) `(x,a) ↦ r(x,a)` is continuous,
then:
a) `J_∞` is continuous, `J_∞ ∈ IB_b` and `J_∞ = J` (Value Iteration);
b) `J_∞` is the unique continuous fixed point of `T` in `IB_b`;
c) `∅ ≠ Ls D*_n(x) ⊂ D*_∞(x)` for all `x ∈ E` (Policy Iteration);
d) there exists `f* ∈ F` with `f*(x) ∈ Ls D*_n(x)` for all `x ∈ E`, and the stationary policy
   `(f*, f*, …)` is optimal.

Here (p.201) `D*_n(x) := {a ∈ D(x) | a is a maximum point of a ↦ L J_{n−1}(x,a)}` for
`n ∈ ℕ ∪ {∞}` (with `J_{∞−1} := J_∞`) and `Ls D*_n(x)` is the set of accumulation points of
sequences `(a_n)` with `a_n ∈ D*_n(x)` for `n ∈ ℕ`.

**Formalization Note.** A Borel space (Remark 2.1.2 a)) is a Borel subset of a Polish space with
its Borel σ-algebra; it is encoded as a metrizable, second-countable topological space whose
Borel σ-algebra is standard Borel. The model, `IB_b`, `T`, `L`, `J_∞`, `J_n`, `J_{∞π}`, the
maximum-point sets (`Dstar M J x`), the upper limit `LsSeq` and continuity of a set-valued map
(`ContinuousSetValued`, Definition A.2.1, p.351) are the published `MDPFinance.Contracting`
bundles. Since `Q` and `r` are given on `D`, the continuity in (ii) and (iii) is continuity on
`D` (`ContinuousOn … M.D`). The sequence `n ↦ D*_{n+1}(x) = Dstar M (J_n) x`, `n ≥ 0`, indexes
`D*_n`, `n ≥ 1`; a shift does not change the accumulation points. `J_∞ = J` is stated as
`J_n(x) → J_∞(x)` in `EReal`; `J_∞ ∈ IB_b` and continuity are stated for its real version,
together with `J_∞` being real-valued. Optimality of `(f*, f*, …)` is
`J_{∞ f*^∞}(x) = J_∞(x)` for all `x`. -/
theorem theorem_7_3_6 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [TopologicalSpace E] [TopologicalSpace A]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E] [BorelSpace E]
    [StandardBorelSpace E]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A]
    [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hbcont : Continuous b) (hβαb : M.β * αb < 1)
    (hDcompact : ∀ x, IsCompact (M.Dx x)) (hDcont : ContinuousSetValued M.Dx)
    (hQcont : ∀ v ∈ IBb b, Continuous v →
      ContinuousOn (fun p : E × A => ∫ x', v x' ∂(M.Q p)) M.D)
    (hrcont : ContinuousOn M.r M.D) :
    -- a) Value iteration
    ((∀ x, Jinf M x = (((Jinf M x).toReal : ℝ) : EReal)) ∧
        Continuous (fun x => (Jinf M x).toReal) ∧
        (fun x => (Jinf M x).toReal) ∈ IBb b ∧
        ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x))) ∧
      -- b) unique continuous fixed point of T in IB_b
      (T M (Jinf M) = Jinf M ∧
        ∀ v ∈ IBb b, Continuous v → T M (fun y => (v y : EReal)) = (fun y => (v y : EReal)) →
          ∀ x, (v x : EReal) = Jinf M x) ∧
      -- c) Policy iteration
      (∀ x, (LsSeq (fun n => Dstar M (Jn M M.r n) x)).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      -- d) an optimal stationary policy from the upper limit
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq (fun n => Dstar M (Jn M M.r n) x)) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end BauerleRiederMDP.Contracting
