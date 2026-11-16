-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_7_9
-- name    : AcceptSubcube.Supplement.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:53:30.216958+00:00
-- url     : https://prove2.me/theorems/27965f77-644b-4f07-be60-b1ef87bc7012
-- title:
--   Theorem 7.9 — hardness of complete Min-$k$-SAT under a linear-optimum promise: no $O(n^{1-\varepsilon})$ unless $\mathsf{NP}=\mathsf{RP}$
-- statement:
--   Fix $k\ge4$, $\varepsilon>0$ and $c>0$. Let $\mathcal D$ be the complete unweighted Min-$k$-SAT instances $\mathcal I$ on $n$ variables with
--   $$1\le\mathrm{OPT}(\mathcal I)\le C_{\mathcal I}(\mathbf 1^n)\le n,\qquad\big|\{E:P_E\text{ is not the all-positive clause}\}\big|\le\frac{n}{k-3}.\tag{34}$$
--   If a randomized polynomial-time algorithm outputs, on every instance of $\mathcal D$, an assignment $Y$ with
--   $$\Pr\big[C_{\mathcal I}(Y)\le c\,n^{1-\varepsilon}\,\mathrm{OPT}(\mathcal I)\big]\ge 2/3,\qquad\text{or with}\qquad\mathbb E[C_{\mathcal I}(Y)]\le c\,n^{1-\varepsilon}\,\mathrm{OPT}(\mathcal I),$$
--   then $\mathsf{NP}=\mathsf{RP}$. If a deterministic polynomial-time algorithm achieves $C_{\mathcal I}(Y)\le c\,n^{1-\varepsilon}\mathrm{OPT}(\mathcal I)$ on $\mathcal D$, then $\mathsf P=\mathsf{NP}$.
--
--   Since $\mathcal D$ is contained in the instances with $1\le\mathrm{OPT}\le n$, this also gives the theorem's first form (algorithm on every complete Min-$k$-SAT instance with $1\le\mathrm{OPT}\le n$). At $k=4$ it matches the exponent of Theorem 1.2(b) under a linear-optimum promise.
--
--   **Formalization Note** Complete Min-$k$-SAT is complete signed $\mathrm{THR}_{k,1}$. Machine model and classes as in Theorem 1.2.
--
--   Differences from the source:
--   - reading: a randomized (resp. deterministic) polynomial-time algorithm → a TM2 polynomial-time machine (Turing.TM2ComputableInPolyTime) on (instance, coin string) with coin strings of length p(|enc I|) for a polynomial p fixed before the instance, probabilities and expectations taken over the exact uniform distribution on those coin strings (resp. a TM2 polynomial-time machine on the instance alone); reason: the paper names no machine model; fair coins are its model (p.28); this is the convention of the published theorem_1_1
--   - encoding: NP, RP, BPP, P and the UGC → the classes of the published CookPvsNP model over every finite alphabet (RP and BPP as polynomial-time checking relations on (input, coin string) with coin strings of length |w|^k + k), and the published OptInapprox.MaxCut.UGC; reason: one machine model for every class in a statement, the model of the published UGC; these are the standard classes
--   - reading: an algorithm on every complete unweighted Min-k-SAT instance with 1 ≤ OPT(I) ≤ n … It suffices that the algorithm work on instances that additionally satisfy (34) → the algorithm is assumed only on the instances satisfying 1 ≤ OPT and (34); reason: the theorem's 'it suffices' form, which implies its first form because OPT ≤ C_I(1ⁿ) always holds
--   - encoding: |{E : P_E is not the all-positive clause}| ≤ n/(k − 3) → (k − 3) · count ≤ n over the reals; reason: real division; no natural-number truncation
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 7.9, p.40 (proof: Lemmas 7.10, 7.11, Proposition 7.12, p.41)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_Supplement_RP
import Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
import Definitions.Def_AcceptSubcube_Supplement_RandApproxOn

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 7.9 (Hardness under a linear-optimum promise).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 7.9, p.40: "Fix k ≥ 4 and ε > 0. If a
randomized polynomial-time algorithm outputs, on every complete unweighted Min-k-SAT instance with
1 ≤ OPT(I) ≤ n, an assignment Y with P[C_I(Y) ≤ c n^{1−ε} OPT(I)] ≥ 2/3, or with
E[C_I(Y)] ≤ c n^{1−ε} OPT(I), for a constant c > 0, then NP = RP. It suffices that the algorithm
work on instances that additionally satisfy OPT(I) ≤ C_I(1_n) ≤ n,
|{E : P_E is not the all-positive clause}| ≤ n/(k − 3). (34) For deterministic algorithms the
conclusion is P = NP."

For `k ≥ 4`, `ε > 0`, `c > 0`, let `D` be the complete unweighted Min-`k`-SAT instances with
`1 ≤ OPT`, `C_I(1_n) ≤ n` and at most `n/(k − 3)` constraints other than the all-positive clause.
A randomized polynomial-time algorithm on `D` with `P[C_I(Y) ≤ c n^{1−ε} OPT] ≥ 2/3`, or with
`E[C_I(Y)] ≤ c n^{1−ε} OPT`, gives `NP = RP`; a deterministic `c n^{1−ε}`-approximation on `D`
gives `P = NP`.

**Formalization Note.** Complete Min-`k`-SAT is `CompleteSigned (thr 1) k` (one `k`-clause on every
`k`-set). The algorithm is assumed only on the promise family `D` (the "it suffices" form, which
implies the first form: `OPT ≤ C_I(1_n)` always holds, so `D` is contained in the instances with
`1 ≤ OPT ≤ n`). The count bound `≤ n/(k − 3)` is stated over the reals as
`(k − 3)·count ≤ n`. Algorithms and classes as in `theorem_1_2`. -/
theorem theorem_7_9 :
    ∀ k : ℕ, 4 ≤ k → ∀ ε c : ℝ, 0 < ε → 0 < c →
      let D : GInst → Prop := fun I => CompleteSigned (thr 1) k I ∧ 1 ≤ OPT I ∧
        cost I (fun _ => true) ≤ I.n ∧ ((k : ℝ) - 3) * (numNotAllPos I : ℝ) ≤ (I.n : ℝ)
      let ρ : GInst → ℝ := fun I => c * (I.n : ℝ) ^ (1 - ε)
      (RandApproxOn D ρ (2 / 3) → NPeqRP) ∧
      (RandApproxExpOn D ρ → NPeqRP) ∧
      (DetApproxOn D ρ → PeqNP) := by sorry

end AcceptSubcube.Supplement
