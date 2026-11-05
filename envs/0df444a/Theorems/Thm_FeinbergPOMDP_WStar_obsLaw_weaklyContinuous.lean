-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_obsLaw_weaklyContinuous
-- name    : FeinbergPOMDP.WStar.obsLaw_weaklyContinuous
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T18:22:42.154606+00:00
-- url     : https://prove2.me/theorems/15cb1832-5673-49cd-be83-519cdf83d550
-- title:
--   $R'$ is weakly continuous when $P$ and $Q$ are weakly continuous
-- statement:
--   Let $\mathbb X,\mathbb Y,\mathbb A$ be separable metrizable spaces with their Borel $\sigma$-algebras, $P(dx'\mid x,a)$ a stochastic kernel on $\mathbb X$ given $\mathbb X\times\mathbb A$ and $Q(dy\mid a,x)$ a stochastic kernel on $\mathbb Y$ given $\mathbb A\times\mathbb X$. Consider the observation kernel (3.2)
--   $$R'(C\mid z,a)=\int_{\mathbb X}\int_{\mathbb X}Q(C\mid a,x')\,P(dx'\mid x,a)\,z(dx),\qquad C\in\mathcal B(\mathbb Y),\ z\in\mathbb P(\mathbb X),\ a\in\mathbb A .$$
--
--   If $P$ and $Q$ are weakly continuous, then $R'$ is weakly continuous on $\mathbb P(\mathbb X)\times\mathbb A$: whenever $z^{(n)}\to z$ weakly and $a^{(n)}\to a$, the measures $R'(\cdot\mid z^{(n)},a^{(n)})$ converge weakly to $R'(\cdot\mid z,a)$.
--
--   This is the weak continuity of $R'$ used in the proof of Theorem 3.5 under condition (ii) of Theorem 3.2; the paper attributes it to Hernández-Lerma (1989, p. 92).
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, proof of Theorem 3.5, p. 17 ('the weak continuity of the stochastic kernel R' on Y given P(X) x A (this weak continuity is proved in Hernandez-Lerma [18, p. 92])')

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, proof of Theorem 3.5 (p. 17): if the
stochastic kernels `P(dx′ | x, a)` and `Q(dy | a, x)` are weakly continuous, then the observation
kernel `R′(dy | z, a)` of (3.2) on `𝕐` given `ℙ(𝕏) × 𝔸` is weakly continuous (proved in
Hernández-Lerma [18, p. 92], cited there). -/
theorem obsLaw_weaklyContinuous {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsWeaklyContinuous (kernelPM Q)) :
    IsWeaklyContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by sorry

end FeinbergPOMDP.WStar
