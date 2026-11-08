-- Prove2me | Theorems.Thm_AvoidPlast_theorem_5_12
-- name    : AvoidPlast.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:13.86003+00:00
-- url     : https://prove2.me/theorems/b7dd0a09-ed8f-40f7-88d7-389f754ab56e
-- title:
--   Theorem 5.12 — low-space PCP proofs for sublinear time from hardness of Avoid
-- statement:
--   For every $c>1$ the following holds. For sufficiently small constants $\varepsilon>\delta>0$, every $L\in\mathrm{NTIME}[n^\varepsilon]$, every $q$ with $n^{c\varepsilon}\le q(n)\le n$ and every PCP system for $L$ whose parameters match Theorem 4.1, with any soundness error $s(n)<1$ (the proof uses $1/2$) and proof length at most $n^{c\varepsilon}$, there is a non-deterministic polynomial-time algorithm $A$ that uses $O(n^\varepsilon)$ non-deterministic bits and outputs a $q(n)$-bit string on each accepting path, such that for every indexed family $C[n^\delta\to q(n)]$ evaluable in space $O(n^\delta)$ there is a deterministic machine $M_{L,C}$ using space $O(n^\delta)$ with, for every sufficiently large $n$ and every $x\in\{0,1\}^n$:
--
--   1. if $M_{L,C}(x)\ne\bot$, then $M_{L,C}(x)$ outputs a PCP proof $\pi_x$ such that $V^{\pi_x}(x)$ accepts with probability $1$;
--   2. if $x\notin L$, then $M_{L,C}(x)=\bot$;
--   3. if $x\in L$ and $M_{L,C}(x)=\bot$, then $A(x)$ solves Avoid$_C$.
--
--   Consequently, for any distributions $D_n$ on $\{0,1\}^n$ and $p:\mathbb N\to[0,1]$, if $\Pr_{x\sim D_n}[A(x)\text{ solves Avoid}_C]\le p(n)$ for all large $n$, then $\Pr_{x\sim D_n}[x\in L\text{ and }M_{L,C}(x)=\bot]\le p(n)$. Moreover, if $L\in\mathrm{DTIME}[n^\varepsilon]$, then $A$ can be made deterministic and total, outputting a $q(n)$-bit string on every $n$-bit input.
--
--   This is the reconstruction at the heart of the main theorem: hardness of Avoid for $A$ means that $M_{L,C}$ prints proofs on most inputs.
--
--   Differences from the source:
--   - generalization: there is a universal constant $c>1$ → every $c>1$, the PCP system having proof length at most $n^{c\varepsilon}$; reason: the proof fixes $c$ with the PCP system (p.28) and uses nothing else about it; (2)⇒(1) picks $c$ large for the PCP it uses (p.30)
--   - generalization: the verifier $V_{PCP}$ with soundness error $1/2$ (p.28), for "every PCP verifier $V$ whose parameters match those in Theorem 4.1" → any soundness error $s(n)<1$; reason: Items 1–3 use only that every proof of an $x\notin L$ is rejected on some random string; $s=1/2$ is an instance, and a verifier with $s\ge1$ would make Item 2 false
--   - reading: $A$ is chosen before "every PCP verifier $V$ whose parameters match those in Theorem 4.1" → the PCP system, with its honest-proof machine, is chosen first and $A$ depends on it; reason: the proof begins "Fix a PCP system" and builds $A$ from its honest proofs, and the goal applies it "using the PCP above"; reading R6
--   - reading: "every PCP verifier $V$ whose parameters match those in Theorem 4.1" → a PCP system (`IsPCPSystem`) that also uses $\mathrm{polylog}(n)$ random bits and has nice proof and randomness lengths; reason: the proof enumerates the random strings, "using $r(n)=\mathrm{polylog}(n)$ random bits" (p.28), and computes the lengths $n_0$ and $r(n)$; Theorem 4.1 as formalized provides these clauses
--   - reading: "every $q:\mathbb N\to\mathbb N$"; constants $\varepsilon,\delta$ → $q$, $\lceil n^\varepsilon\rceil$ and $\lceil n^\delta\rceil$ nice; reason: Definition 3.3 imposes niceness on the lengths $\lceil n^\delta\rceil$ and $q$ of an evaluable family (p.14), $A$ must print $q(n)$ bits, and $A$ must enforce the witness bound $C_0(\lceil n^\varepsilon\rceil+1)$ on its non-deterministic bits; for rational $\varepsilon,\delta$, the case the goal uses, $\lceil n^\varepsilon\rceil$ and $\lceil n^\delta\rceil$ are nice
--   - encoding: $A$ uses at most $n^\varepsilon$ non-deterministic bits → $|w|\le C_0(\lceil n^\varepsilon\rceil+1)$, the witness bound of $L$'s verifier; reason: the witness of $L\in\mathrm{NTIME}[n^\varepsilon]$ is $O(n^\varepsilon)$ bits (p.18)
--   - reading: $L\in\mathrm{DTIME}[n^\varepsilon]$ → the verifier of $L$ accepts every $x\in L$ with the empty witness; reason: the "moreover" part computes "the canonical accepting PCP proof" (p.29), which is the fixed system's honest proof from the witness of the given verifier; the goal applies it to the verifier of $L_{pad}$, which needs no witness
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - encoding: indexed family of circuits $C[\ell_{in}\to\ell_{out},s]$ with $s$ arbitrary → a map $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$; reason: every such map has a circuit and the size is unconstrained; reading R8
--   - encoding: "$A(x)$ solves Avoid$_C$" for non-deterministic $A$ → a path accepts, and every accepting path outputs a solution; reason: the convention of the proof, p.28
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.12, pp.27–28

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_IsNice
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_PCPSystem
import Definitions.Def_AvoidPlast_IsPCPSystem
import Definitions.Def_AvoidPlast_SolvesAvoidND
import Definitions.Def_AvoidPlast_PrintsProofs

namespace AvoidPlast

/-- Theorem 5.12, low-space PCP proofs for sublinear time from hardness of Avoid (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), pp.27–28). Fix a
PCP system for `L ∈ NTIME[n^ε]` with the parameters of Theorem 4.1, any soundness error `s(n) < 1`
(the proof uses `1/2`) and proof length `≤ n^{cε}`, and `q` with `n^{cε} ≤ q(n) ≤ n`. There is a non-deterministic polynomial-time `A`,
using `O(n^ε)` non-deterministic bits and printing `q(n)` bits on each accepting path, such that for
every family `C[n^δ → q(n)]` evaluable in space `O(n^δ)` there is a deterministic machine `M` of space
`O(n^δ)` with items 1–3 and the "Consequently" clause (`PrintsProofs`). Moreover, if `L ∈ DTIME[n^ε]`
then `A` can be made deterministic and total.

**Formalization Note** Reading R6: the PCP system comes before `A`, as the proof fixes it first. The
lengths are *nice*, the paper's convention (p.14). `L ∈ DTIME[n^ε]` is that `V₀` accepts every `x ∈ L`
with the empty witness. -/
theorem theorem_5_12 : ∀ c : ℝ, 1 < c → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ : ℝ, 0 < δ → δ < ε → ε < ε₀ →
    IsNice (ceilPow ε) → IsNice (ceilPow δ) →
    ∀ (L : Set (List Bool)) (V₀ : Machine 2) (C₀ : ℕ), IsNTimeVerifier V₀ L (ceilPow ε) C₀ →
    ∀ q : ℕ → ℕ, IsNice q → (∀ n : ℕ, (n : ℝ) ^ (c * ε) ≤ q n ∧ q n ≤ n) →
    ∀ s : ℕ → ℝ, (∀ n : ℕ, s n < 1) →
    ∀ S : PCPSystem, IsPCPSystem S L V₀ (ceilPow ε) C₀ s →
    (∀ᶠ n : ℕ in Filter.atTop, (S.proofLen n : ℝ) ≤ (n : ℝ) ^ (c * ε)) →
    (∃ (A : Machine 2) (a : ℕ),
      (∀ x w : List Bool, HaltsWithin A ![x, w] (a * (x.length ^ a + 1))) ∧
      (∀ x w : List Bool, Accepts A ![x, w] →
        w.length ≤ C₀ * (ceilPow ε x.length + 1) ∧ (output A ![x, w]).length = q x.length) ∧
      ∀ Cf : List Bool → List Bool → List Bool,
        EvaluableInSpace Cf (ceilPow δ) q (fun n => (n : ℝ) ^ δ) →
        ∃ M : Machine 1, SpaceO M (fun n => (n : ℝ) ^ δ) ∧
          PrintsProofs S L (SolvesAvoidND A Cf (ceilPow δ) q) M) ∧
    ((∀ x ∈ L, Accepts V₀ ![x, []]) →
      ∃ A : Machine 1, PolyTime A ∧ (∀ x : List Bool, (output A ![x]).length = q x.length) ∧
      ∀ Cf : List Bool → List Bool → List Bool,
        EvaluableInSpace Cf (ceilPow δ) q (fun n => (n : ℝ) ^ δ) →
        ∃ M : Machine 1, SpaceO M (fun n => (n : ℝ) ^ δ) ∧
          PrintsProofs S L (fun x => SolvesAvoid Cf (ceilPow δ) q x (output A ![x])) M) := by sorry

end AvoidPlast
