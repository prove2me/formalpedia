-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_1_4
-- name    : AcceptSubcube.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:51:03.908889+00:00
-- url     : https://prove2.me/theorems/6b40f18d-6200-499a-b230-4ce797306051
-- title:
--   Theorem 1.4 — Boolean Turán networks: $O(1)$, $O(\sqrt{\log(\mathrm{OPT}+2)})$, $O((n/\log(n+2))^{k-3})$
-- statement:
--   Fix integers $q\ge k\ge2$. There is a constant $A_{k,q}>0$, depending only on $k$ and $q$, such that:
--
--   1. A randomized polynomial-time algorithm outputs, on every Boolean Turán network $\mathcal I$ with parameters $(k,q)$ (Definition 6.1), with probability at least $1-(n+2)^{-10}$, an assignment $Y$ with
--   $$C_{\mathcal I}(Y)\le\begin{cases}A_{k,q}\,\mathrm{OPT},&k=2,\\ A_{k,q}\sqrt{\log(\mathrm{OPT}+2)}\;\mathrm{OPT},&k=3,\\ A_{k,q}\big(n/\log(n+2)\big)^{k-3}\,\mathrm{OPT},&k\ge4;\end{cases}$$
--   and when $\mathrm{OPT}=0$ its output is optimal and the same for every coin string.
--   2. For all $c>0$ and $0<\delta\le1$, a randomized polynomial-time algorithm outputs, on every such network with $\mathrm{OPT}\le c\log^k(n+2)$, with probability at least $1-(n+2)^{-10}$, an assignment of cost at most $(1+\delta)\,\mathrm{OPT}$.
--
--   This extends the arbitrary-predicate case of Theorem 1.1 from complete instances to instances in which every $q$-set of variables contains a constrained scope.
--
--   **Formalization Note** Machine model and coin strings as in Theorem 1.1. Natural logarithms.
--
--   Differences from the source:
--   - reading: a randomized (resp. deterministic) polynomial-time algorithm → a TM2 polynomial-time machine (Turing.TM2ComputableInPolyTime) on (instance, coin string) with coin strings of length p(|enc I|) for a polynomial p fixed before the instance, probabilities and expectations taken over the exact uniform distribution on those coin strings (resp. a TM2 polynomial-time machine on the instance alone); reason: the paper names no machine model; fair coins are its model (p.28); this is the convention of the published theorem_1_1
--   - reading: The case OPT = 0 is solved exactly and deterministically → when OPT = 0 the output is optimal and the same for every coin string of the given length; reason: the coin string is part of the machine's input; the zero-optimum branch uses no coin (p.33)
--   - reading: a randomized polynomial-time algorithm also gives a (1 + δ)-approximation (probability not restated) → probability at least 1 − (n+2)^{−10}; reason: the theorem's own success probability; the proof amplifies every branch to it (p.34)
--   - encoding: Boolean Turán network with parameters (k, q) → a raw constraint list (GInst) that is well formed, k-uniform, has at most one constraint per scope and only nontrivial predicates, and in which every q-subset of [n] contains a scope; reason: Definition 6.1 verbatim on the mission's instance type; no instance is added or removed
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.4, p.6; Definition 6.1, p.30; proof §6.4, pp.33–34

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac
import Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
import Definitions.Def_AcceptSubcube_Supplement_RandApproxOn

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 1.4 (Boolean Turán networks).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.4, p.6: "For all fixed q ≥ k ≥ 2, a
randomized polynomial-time algorithm outputs on every such network an assignment Y with probability
at least 1 − (n + 2)^{−10} satisfying C_I(Y) ≤ A_{k,q} OPT (k = 2), A_{k,q} √log(OPT + 2) OPT
(k = 3), A_{k,q} (n/log(n + 2))^{k−3} OPT (k ≥ 4), where A_{k,q} depends only on k, q. The case
OPT = 0 is solved exactly and deterministically. For fixed c > 0 and 0 < δ ≤ 1, a randomized
polynomial-time algorithm also gives a (1 + δ)-approximation when OPT ≤ c log^k(n + 2)."

For all `q ≥ k ≥ 2` there is `A_{k,q} > 0` such that:
1. a polynomial-time machine on (instance, coin string) outputs, on every Boolean Turán network
   with parameters `(k, q)` (Definition 6.1), with probability at least `1 − (n+2)^{−10}`, an
   assignment within `ratio14 k A_{k,q}`; and when `OPT = 0` its output is optimal and the same for
   every coin string;
2. for all `c > 0` and `0 < δ ≤ 1`, a polynomial-time machine outputs, on every such network with
   `OPT ≤ c log^k(n + 2)`, with probability at least `1 − (n+2)^{−10}`, an assignment of cost at
   most `(1 + δ) OPT`.

**Formalization Note.** Machine model and coin strings as in the published `theorem_1_1`. "Solved
exactly and deterministically" is read as: optimal output, independent of the coin string. The
`(1 + δ)` clause does not restate its probability; it is read with the theorem's probability
`1 − (n+2)^{−10}` (the proof's amplification, p.34). `A_{k,q}` is chosen before `c`, `δ`; the second
machine may depend on `(c, δ)`. -/
theorem theorem_1_4 :
    ∀ k q : ℕ, 2 ≤ k → k ≤ q → ∃ A : ℝ, 0 < A ∧
      (∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
        Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
        ∀ I : GInst, TuranNet k q I →
          (1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
            coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ ratio14 k A I)) ∧
          (OPT I = 0 → ∀ w w' : List Bool, w.length = p.eval (encInst I).length →
            w'.length = p.eval (encInst I).length →
            alg (I, w) = alg (I, w') ∧ cost I (asg I (alg (I, w))) = OPT I)) ∧
      ∀ c δ : ℝ, 0 < c → 0 < δ → δ ≤ 1 →
        ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
          Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
          ∀ I : GInst, TuranNet k q I →
            (OPT I : ℝ) ≤ c * Real.log ((I.n : ℝ) + 2) ^ k →
            1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
              coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ (1 + δ) * (OPT I : ℝ)) := by sorry

end AcceptSubcube.Supplement
