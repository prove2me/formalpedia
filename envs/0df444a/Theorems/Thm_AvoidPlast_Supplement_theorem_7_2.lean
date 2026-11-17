-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_7_2
-- name    : AvoidPlast.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:54:48.93434+00:00
-- url     : https://prove2.me/theorems/8c85ab65-fcd1-465e-af65-4afff5d9e142
-- title:
--   Theorem 7.2 — no targeted HSG with few outputs against coNP linear time
-- statement:
--   Let $m(n)<n$, $k(n)=m(n)\cdot2^{j(n)}<n$ (so $k/m$ is a power of two) with $\log(k/m)+1<m$, and let $\mathcal D$ be the class of co-non-deterministic linear-time machines using $m(n)$ bits of randomness on inputs of length $n$. Assume that every non-deterministic machine $M$ fails to solve Avoid on some circuit $C:\{0,1\}^{m-\lceil\log(k/m)\rceil-1}\to\{0,1\}^k$ of size $n$, that is, $M(C)$ rejects all witnesses or outputs on some witness a string in the range of $C$. Then there is no SearchNP-computable targeted $(1/2)$-HSG against $\mathcal D$ that on $n$-bit inputs has seed length $\log(k/m)$ and output length $m$.
--
--   Under worst-case hardness of Avoid this answers Goldreich's question negatively for generators with few outputs.
--
--   Differences from the source:
--   - generalization: "for every non-deterministic machine $M$" → for every non-deterministic polynomial-time machine $M$; reason: a weaker hypothesis; the proof applies it only to the polynomial-time algorithm built from the generator
--   - reading: "there is $C$ ... of size $n$" → for infinitely many $n$ there is an $n$-bit circuit description; reason: matches "$n$ sufficiently large" in Definition 7.1
--   - encoding: "$C$ of size $n$" → an $n$-bit description under the fixed-width encoding `decodeCircuit`; reason: the paper fixes no encoding; this one is linear-time parseable, as the proof's distinguisher needs
--   - encoding: $k$ with $k/m$ a power of two → $k=m\cdot2^j$ and seed length $j$; reason: the same parameters
--   - reading: $m(n)<n$, $k(n)<n$, $\log(k/m)+1<m$ → required for every sufficiently large $n$; reason: at $n=0$ the constraint $k(n)<n$ is unsatisfiable, so "for every $n$" would make the theorem vacuous
--   - encoding: co-non-deterministic linear-time machines using $m(n)$ random bits → a machine $D(x,r,w)$ halting within $K(|x|+1)$ steps for $|r|=m(|x|)$; $D(x,r)=1$ iff every $w$ with $|w|\le K(|x|+1)$ is accepted; reason: Definition 3.7 with a linear time bound
--   - reading: a SearchNP-computable targeted HSG (Definition 7.1 extended to non-deterministic $G$) → on every input some witness is accepted, every accepting path outputs $2^j$ strings of $m$ bits, and for large $n$ every accepting path hits every $D$ with $\Pr_r[D=1]\ge1/2$; reason: Definition 7.1 and the proof: "for every $C$ there is a witness causing $H(C)$ to output a list"
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.2, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_Circuit
import Definitions.Def_AvoidPlast_Supplement_Circuit_eval
import Definitions.Def_AvoidPlast_Supplement_decodeCircuit
import Definitions.Def_AvoidPlast_Supplement_coNDAccepts
import Definitions.Def_AvoidPlast_Supplement_IsSearchNPGen
import Definitions.Def_AvoidPlast_Supplement_HitsTargeted

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 7.2 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.40). Let `m(n) < n`, `k(n) = m(n)·2^{j(n)} < n` (so `k/m = 2^j` is a power
of two) with `j + 1 < m`, and let `D` be the class of co-non-deterministic linear-time machines
using `m(n)` random bits. Assume that every non-deterministic (polynomial-time) machine `M` fails to
solve Avoid on some circuit `C : {0,1}^{m - j - 1} → {0,1}^k` of size `n`, i.e. `M(C)` rejects all
witnesses or outputs on some witness a string in the range of `C`. Then there is no
SearchNP-computable targeted `(1/2)`-HSG against `D` that on `n`-bit inputs has seed length `j`
(`2^j` outputs) and output length `m`.

**Formalization Note** "Size `n`" is an `n`-bit description under `decodeCircuit`; the assumption is
required for infinitely many `n`, matching "sufficiently large `n`" in Definition 7.1. The parameter
constraints are required for every sufficiently large `n` (at `n = 0`, `m(n) < n` is impossible). -/
theorem theorem_7_2 (m j : ℕ → ℕ)
    (hmk : ∀ᶠ n : ℕ in Filter.atTop, m n < n ∧ m n * 2 ^ j n < n ∧ j n + 1 < m n)
    (hyp : ∀ (M : Machine 2) (a : ℕ), IsPolyNTime M a → ∃ᶠ n : ℕ in Filter.atTop,
      ∃ c : List Bool, c.length = n ∧ ∃ circ : Circuit, decodeCircuit c = some circ ∧
        circ.nIn = m n - j n - 1 ∧ circ.outs.length = m n * 2 ^ j n ∧
        ((∀ w : List Bool, w.length ≤ a * (n ^ a + 1) → ¬ Accepts M ![c, w]) ∨
          ∃ w : List Bool, w.length ≤ a * (n ^ a + 1) ∧ Accepts M ![c, w] ∧
            ∃ z : List Bool, z.length = circ.nIn ∧ circ.eval z = output M ![c, w])) :
    ¬ ∃ (H : Machine 2) (a : ℕ), IsSearchNPGen H a (fun n => 2 ^ j n) m ∧
      ∀ (D : Machine 3) (K : ℕ),
        (∀ x r w : List Bool, r.length = m x.length → HaltsWithin D ![x, r, w] (K * (x.length + 1))) →
        HitsTargeted H a (fun n => 2 ^ j n) m (fun x r => coNDAccepts D (K * (x.length + 1)) x r)
          (1 / 2) := by sorry

end AvoidPlast.Supplement
