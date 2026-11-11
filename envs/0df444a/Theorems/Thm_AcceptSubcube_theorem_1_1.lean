-- Prove2me | Theorems.Thm_AcceptSubcube_theorem_1_1
-- name    : AcceptSubcube.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:25.452844+00:00
-- url     : https://prove2.me/theorems/8501d7a8-5e41-4fde-9149-02e83692e160
-- title:
--   Theorem 1.1 — randomized polynomial-time approximation of $\mathcal C_{k,h}$
-- statement:
--   Fix integers $k\ge2$ and $1\le h\le k-1$, and put $\Pi=\binom{n}{k-h-1}$. There is a constant $A_k>0$ depending only on $k$ such that, for all $c,\delta>0$, a randomized polynomial-time algorithm has the following three properties on every instance $\mathcal I$ of $\mathcal C_{k,h}$:
--
--   1. with probability at least $1-(n+2)^{-10}$ it outputs an assignment $Y$ with
--   $$C_{\mathcal I}(Y)\le\begin{cases}A_k\,\mathrm{OPT},&h=1,\\ A_k\sqrt{\log(2+\mathrm{OPT}/\Pi)}\;\mathrm{OPT},&h=2,\\ A_k\big(n/\log(n+2)\big)^{h-2}\,\mathrm{OPT},&h\ge3;\end{cases}$$
--   2. it is exact and deterministic when $\mathrm{OPT}\le\Pi$: its output is optimal and the same for every coin string;
--   3. it gives a $(1+\delta)$-approximation when $\mathrm{OPT}\le c\,\Pi\log^{h+1}(n+2)$, with probability at least $1-(n+2)^{-10}$.
--
--   For $h=k-1$ ($\Pi=1$) this covers complete $k$-CSPs with arbitrary nontrivial predicates; for $k=3$ it gives an $O(\sqrt{\log(\mathrm{OPT}+2)})$-approximation for complete Boolean 3-CSPs.
--
--   Differences from the source:
--   - reading: a randomized polynomial-time algorithm … with probability at least → a TM2 polynomial-time machine on (instance, coin string), one polynomial p fixed before the instance, coins of length p(|enc I|), probability = exact fraction of coin strings; reason: the paper names no machine model; fair coins are its model (p.28)
--   - reading: an algorithm, and for fixed c, δ a (1 + δ)-approximation → one machine per (c, δ) carrying all three clauses, A_k chosen before h, c, δ; reason: stronger than separate algorithms (take c = δ = 1 for the main one); the paper's trial runs all branches and keeps the cheapest (§5.4)
--   - reading: the (1 + δ)-approximation (probability not restated) → probability at least 1 − (n+2)^{−10}; reason: Theorem 1.1 is Theorem 5.1 with ζ = (n+2)^{−10} (p.25), proved with ζ for all clauses (p.28)
--   - reading: exact and deterministic when OPT ≤ Π → the output is optimal and the same for every coin string; reason: the coin string is part of the machine's input; the exact branch uses no coin (§5.4 (1))
--   - encoding: instances of C_{k,h}, assignments → raw constraint lists (GInst) satisfying InClass k h, every n allowed (n < k: no constraints); outputs are bit lists read as assignments; reason: data must be encodable; no instance of the class is added or removed
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_subcubeDim
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac
import Definitions.Def_AcceptSubcube_ratio11

namespace AcceptSubcube

/-- **Theorem 1.1 (Algorithms).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4: "Fix integers k ≥ 2 and
1 ≤ h ≤ k − 1, and put Π = (n choose k−h−1). There is a randomized polynomial-time algorithm that,
on every instance of 𝒞_{k,h}, outputs with probability at least 1 − (n + 2)^{−10} an assignment Y
with C_I(Y) ≤ A_k OPT (h = 1), A_k √log(2 + OPT/Π) OPT (h = 2), A_k (n/log(n + 2))^{h−2} OPT
(h ≥ 3), for a constant A_k depending only on k. It is exact and deterministic when OPT ≤ Π, and for
fixed c, δ > 0 it gives a (1 + δ)-approximation when OPT ≤ c Π log^{h+1}(n + 2)."

For every `k ≥ 2` there is `A_k > 0` such that for every `1 ≤ h ≤ k − 1` and every `c, δ > 0` there
are a polynomial `p` and a polynomial-time machine reading an instance and a coin string such that,
on every instance `I` of `𝒞_{k,h}` (coin strings of length `p(|enc I|)`, uniform):
1. with probability at least `1 − (n+2)^{−10}` the output `Y` satisfies the three-case bound;
2. if `OPT ≤ Π`, the output is the same for every coin string and is optimal;
3. if `OPT ≤ c Π log^{h+1}(n + 2)`, with probability at least `1 − (n+2)^{−10}` the output costs at
   most `(1 + δ) OPT`.

**Formalization Note.** A randomized polynomial-time algorithm is a TM2 machine
(`Turing.TM2ComputableInPolyTime`) on (instance, coin string), for one polynomial `p` fixed before
the instance; the probability is the exact fraction of the `2^N` coin strings of length
`N = p(|enc I|)` (`coinProb`). One machine per `(c, δ)` carries all three clauses (this implies the
reading with a separate main algorithm). "Exact and deterministic" is read as: optimal output,
independent of the coin string. Instances are raw constraint lists (`GInst`); `𝒞_{k,h}` is
`InClass k h` (complete, nontrivial predicates, accepting-subcube dimension `≤ h`), every `n`
allowed (`n < k`: no constraints). Outputs are read as assignments by `asg`. Natural logarithms
(p.9). `A_k` is chosen after `k` and before `h`, `c`, `δ`. -/
theorem theorem_1_1 :
    ∀ k : ℕ, 2 ≤ k → ∃ A : ℝ, 0 < A ∧
    ∀ h : ℕ, 1 ≤ h → h ≤ k - 1 → ∀ c δ : ℝ, 0 < c → 0 < δ →
    ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
      ∀ I : GInst, InClass k h I →
        (1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
          coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ ratio11 k h A I)) ∧
        ((OPT I : ℝ) ≤ (I.n.choose (k - h - 1) : ℝ) →
          ∀ w w' : List Bool, w.length = p.eval (encInst I).length →
            w'.length = p.eval (encInst I).length →
            alg (I, w) = alg (I, w') ∧ cost I (asg I (alg (I, w))) = OPT I) ∧
        ((OPT I : ℝ) ≤ c * (I.n.choose (k - h - 1) : ℝ) * Real.log ((I.n : ℝ) + 2) ^ (h + 1) →
          1 - ((I.n : ℝ) + 2) ^ (-10 : ℤ) ≤
            coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ (1 + δ) * (OPT I : ℝ))) := by sorry

end AcceptSubcube
