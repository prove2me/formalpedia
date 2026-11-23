-- Prove2me | Theorems.Thm_FeinbergPOMDP_WStar_Supplement_theorem_8_2
-- name    : FeinbergPOMDP.WStar.Supplement.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:31:55.186907+00:00
-- url     : https://prove2.me/theorems/332bc0f1-3c3c-4b41-8167-e598b4accc09
-- title:
--   Theorem 8.2 (corrected: K-restricted level sets in (iv)) — equicontinuity of 𝒫*_𝒪 makes an MDMII satisfy (a), (b), (c)(i) of Theorem 3.2
-- statement:
--   An MDMII (§8.3) has observed states $\mathbb Y$, unobserved states $\mathbb W$ and actions $\mathbb A$, all Borel subsets of Polish spaces; nonempty Borel sets $A(y)\subseteq\mathbb A$ of available actions whose graph $\{(y,a):a\in A(y)\}$ is Borel and has a measurable selector; a weakly continuous transition kernel $P$ on $\mathbb X=\mathbb Y\times\mathbb W$ given $\mathbb X\times\mathbb A$; and a bounded-below Borel cost $c$ on $G=\{(y,w,a):a\in A(y)\}$ that is $\mathbb K$-inf-compact on $G$: for every compact $K\subseteq\mathbb Y\times\mathbb W$ and $\lambda\in\mathbb R$, the set $\{(y,w,a)\in G:(y,w)\in K,\ c(y,w,a)\le\lambda\}$ is compact. It is the POMDP $(\mathbb X,\mathbb Y,\mathbb A,P,Q,c)$ with observation kernel $Q(C|a,(y,w))=\mathbf 1\{y\in C\}$ and with $c=+\infty$ off $G$. For open $\mathcal O\subseteq\mathbb W$ let $\mathcal P^*_{\mathcal O}=\{(x,a)\mapsto P(C\times\mathcal O|x,a):C\in\mathcal B(\mathbb Y)\}$.
--
--   **Theorem 8.2.** Let $\alpha\in[0,1)$, or $\alpha\in[0,1]$ if $c\ge0$. If for every nonempty open $\mathcal O\subseteq\mathbb W$ the family $\mathcal P^*_{\mathcal O}$ is equicontinuous at every point of $\mathbb X\times\mathbb A$, that is,
--   $$\sup_{C\in\mathcal B(\mathbb Y)}\big|P(C\times\mathcal O|x',a')-P(C\times\mathcal O|x,a)\big|\to0\quad\text{as }(x',a')\to(x,a),$$
--   then the POMDP satisfies assumptions (a), (b) and (c)(i) of Theorem 3.2 — (D) or (P) holds, $c$ is $\mathbb K$-inf-compact on $\mathbb X\times\mathbb A$, and $R'$ is setwise continuous and Assumption (H) holds — and therefore the conclusions of Theorem 3.2 hold: the COMDP satisfies Assumption (W*) ($\bar c$ is $\mathbb K$-inf-compact and $q$ weakly continuous) and statements (i)–(vi) of Theorem 3.1 hold.
--
--   The equicontinuity hypothesis is weaker than continuity of $P$ in total variation; it answers Yushkevich's question on the existence of optimal policies for MDMIIs.
--
--   **Formalization Note** The cost is $c=\ell+f$ on $\mathbb X\times\mathbb A$ with $f=+\infty$ off $G$. Equicontinuity at a point is Mathlib's `EquicontinuousAt` for the family indexed by the Borel subsets of $\mathbb Y$. The conclusions about $q$ hold for every filter satisfying (3.3).
--
--   Differences from the source:
--   - encoding: 𝕐, 𝕎, 𝔸 are Borel subsets of Polish spaces → separable metrizable spaces with Borel σ-algebras that are standard Borel; reason: a separable metrizable space is a Borel subset of a Polish space exactly when its Borel σ-algebra is standard; same instances
--   - encoding: a bounded-below cost c : G → ℝ ∪ {+∞}, extended by c = +∞ off G → c = lower + f on 𝕏 × 𝔸 with Borel f : 𝕏 → 𝔸 → [0,∞] and f = ⊤ off G; reason: the MDMII is a POMDP (p. 33), so its cost is bounded below and Borel like every POMDP cost (p. 4), as (a) of Theorem 3.2 under (D) needs; every bounded-below ℝ ∪ {+∞}-valued Borel function has this form; the extension is the one on p. 33
--   - correction: (iv): D_{K,c}(λ) = {(y,w,a) ∈ G : c(y,w,a) ≤ λ} is compact for each compact K ⊆ 𝕐 × 𝕎 → {((y,w),a) : (y,w) ∈ K, a ∈ A(y), c ≤ λ} is compact; reason: the printed set does not depend on K, which would make c inf-compact on G; the subscript K, the name 𝕂-inf-compact and the definition on p. 6 require the restriction (y,w) ∈ K
--   - encoding: expected total discounted costs E Σ α^t c(z_t,a_t) of I-policies, optimal values as infima, integrals of v̄ against q, and 'min' → expectations under the Ionescu Tulcea strategic measure of the published FeinbergLiang.ACOE.MDP, as positive part minus negative part in EReal; 'v = min_a g(a)' as 'some a₀ attains v and v ≤ g(a) for all a'; Markov policies as ℕ-indexed sequences of Borel maps; reason: under (D) the negative parts have finite expectation and under (P) they vanish, so no ∞ − ∞ occurs and these are the paper's quantities; a T-horizon cost does not depend on decision rules after T
--   - encoding: q(D|z,a) = ∫ I{H(z,a,y) ∈ D} R′(dy|z,a) for a stochastic kernel H satisfying (3.3), whose choice does not affect q → statements about q are made for a filter H with IsFilter P Q H (for every such H in the conclusions); the COMDP kernel is q packaged as a Kernel on (ℙ(𝕏), its Borel σ-algebra); reason: p. 8: the choice of H does not affect q; the measurability of (z,a) ↦ q(·|z,a) holds for every filter, so the packaging is exactly q
--   - encoding: Gr(A_{t,α}), Gr(A_α) are Borel subsets of ℙ(𝕏) × 𝔸 → measurable in the product of the Borel σ-algebras of ℙ(𝕏) and 𝔸; reason: both spaces are second countable, so the product σ-algebra is the Borel σ-algebra of the product
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, Theorem 8.2, p. 34 (proof pp. 34–35); MDMII assumptions (i)–(iv), pp. 32–33

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDPValues
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_COMDP
import Definitions.Def_FeinbergPOMDP_WStar_Supplement_MDMII

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

namespace FeinbergPOMDP.WStar.Supplement

/-- Feinberg, Kasyanov, Zgurovsky, arXiv:1401.2168v2, **Theorem 8.2** (p. 34; proof pp. 34–35), for
the MDMII of §8.3 (pp. 32–33): observed states `𝕐`, unobserved states `𝕎`, actions `𝔸`, nonempty
Borel action sets `A(y)` whose graph is Borel and admits a measurable selector, a weakly continuous
transition kernel `P` on `𝕏 = 𝕐 × 𝕎` given `𝕏 × 𝔸`, and a cost `c` on
`G = {(y, w, a) : a ∈ A(y)}` that is `𝕂`-inf-compact on `G` and extended by `+∞` off `G`; the
observation kernel is the projection `Q(C | a, (y, w)) = I{y ∈ C}`. Consider the discount factor
`α ∈ [0, 1)`, and also `α = 1` if `c ≥ 0`. If for every nonempty open `𝒪 ⊆ 𝕎` the family
`𝒫*_𝒪 = {(x, a) ↦ P(C × 𝒪 | x, a) : C ∈ ℬ(𝕐)}` is equicontinuous at all points of `𝕏 × 𝔸`, then
the POMDP `(𝕏, 𝕐, 𝔸, P, Q, c)` satisfies assumptions (a), (b) and (c)(i) of Theorem 3.2, and the
conclusions of that theorem hold: the COMDP satisfies (W*) and statements (i)–(vi) of Theorem 3.1.

Formalization Note. `𝕐, 𝕎, 𝔸` are separable metrizable spaces whose Borel σ-algebras are standard
Borel (Borel subsets of Polish spaces). The cost, bounded below and Borel like every POMDP cost
(p. 4), is `c(x, a) = lower + f x a` on `𝕏 × 𝔸` with `f = +∞` off `G`; `𝕂`-inf-compactness on `G`
(p. 32, (iv)) is stated for every compact `K ⊆ 𝕐 × 𝕎` and real level `λ`, with the points of
the level set restricted to `(y, w) ∈ K` (the printed set `D_{K,c}(λ)` omits this restriction,
which its subscript `K` and the name `𝕂`-inf-compact require). Assumption (a) is the
hypothesis on `α` itself and is restated as the first conclusion; (b) is concluded as `KInfCompact f`; (c)(i) is the
setwise continuity of `R′` together with Assumption (H). Equicontinuity at a point is Mathlib's
`EquicontinuousAt` of the family indexed by Borel `C`, i.e. `sup_C |P(C × 𝒪 | x′, a′) − P(C × 𝒪 | x, a)| → 0`
as `(x′, a′) → (x, a)`. The conclusions about `q` hold for every filter `H` satisfying (3.3). -/
theorem theorem_8_2 {Y W A : Type*}
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [TopologicalSpace W] [TopologicalSpace.MetrizableSpace W] [SecondCountableTopology W]
    [MeasurableSpace W] [BorelSpace W] [StandardBorelSpace W]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (Aset : Y → Set A) (hAne : ∀ y, (Aset y).Nonempty) (hAmeas : ∀ y, MeasurableSet (Aset y))
    (hAgraph : MeasurableSet {p : Y × A | p.2 ∈ Aset p.1})
    (hAsel : ∃ φ : Y → A, Measurable φ ∧ ∀ y, φ y ∈ Aset y)
    (P : Kernel ((Y × W) × A) (Y × W)) [IsMarkovKernel P]
    (hP : IsWeaklyContinuous (kernelPM P))
    (lower α : ℝ) (f : Y × W → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hfG : ∀ (x : Y × W) (a : A), a ∉ Aset x.1 → f x a = ⊤)
    (hKG : ∀ K : Set (Y × W), IsCompact K → ∀ l : ℝ,
      IsCompact {p : (Y × W) × A | p.1 ∈ K ∧ p.2 ∈ Aset p.1.1 ∧
        (lower : EReal) + (f p.1 p.2 : EReal) ≤ (l : EReal)})
    (hDP : (0 ≤ α ∧ α < 1) ∨
      ((∀ (x : Y × W) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧ 0 ≤ α ∧ α ≤ 1))
    (hEq : ∀ O : Set W, IsOpen O → O.Nonempty →
      ∀ p : (Y × W) × A, EquicontinuousAt (PStarFamily P O) p) :
    ((0 ≤ α ∧ α < 1) ∨
      ((∀ (x : Y × W) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧ 0 ≤ α ∧ α ≤ 1)) ∧
    KInfCompact f ∧
    (IsSetwiseContinuous
        (fun p : ProbabilityMeasure (Y × W) × A => obsLaw P (mdmiiObs (A := A)) p.1 p.2) ∧
      AssumptionH P (mdmiiObs (A := A))) ∧
    KInfCompact (beliefCost f) ∧
    ∀ H : ProbabilityMeasure (Y × W) → A → Y → ProbabilityMeasure (Y × W),
      IsFilter P (mdmiiObs (A := A)) H →
        BeliefTransitionWeaklyContinuous P (mdmiiObs (A := A)) H ∧
        COMDPOptimality P (mdmiiObs (A := A)) H lower f α := by sorry

end FeinbergPOMDP.WStar.Supplement
