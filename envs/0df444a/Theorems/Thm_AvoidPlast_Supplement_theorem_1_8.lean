-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_1_8
-- name    : AvoidPlast.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:42:37.739044+00:00
-- url     : https://prove2.me/theorems/9bb92409-edeb-4f38-b762-8cb2129e800a
-- title:
--   Theorem 1.8 (= Corollary 6.7) — hardness of Avoid for tiny-error non-deterministic algorithms
-- statement:
--   Let $g=\{g_n:\{0,1\}^{n-\lceil\log n\rceil-1}\to\{0,1\}^n\}$ be a relaxed $\tfrac14$-demi-bits generator against $\mathsf{AM}$. For $s=(s_1,\dots,s_n)\in\{0,1\}^{n\times n}$ let $C_s:\{0,1\}^{n-1}\to\{0,1\}^n$,
--   $$C_s(x,i)=g(x)\oplus s_i,$$
--   with $i$ written in $\lceil\log n\rceil$ bits and unused codes mapped to $s_1$. Then:
--
--   1. if $g$ is computable in space $s(n)\ge\log n$, the family $\{C_s\}$ (indexed by $s$, of length $N=n^2$) is evaluable in space $O(s(n))$;
--   2. no non-deterministic polynomial-time machine $A$ satisfies, for every sufficiently large $n$,
--   $$\Pr_{s}\bigl[\exists w: A(C_s,w)\in\{0,1\}^n\setminus\mathrm{Range}(C_s)\bigr]\ge3\cdot2^{-n}\quad\text{and}\quad\Pr_{s}\bigl[\forall w: A(C_s,w)\notin\mathrm{Range}(C_s)\bigr]\ge1-2^{-2n}.$$
--
--   In terms of the index length $N=n^2$ this is Theorem 1.8: a non-deterministic algorithm for $\mathrm{Avoid}_C$ that errs on at most $2^{-2\sqrt N}$ of the inputs succeeds on less than $O(2^{-\sqrt N})$ of them.
--
--   Differences from the source:
--   - encoding: $g:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n$ → `g : ℕ → List Bool → List Bool` with `hg`: $g_n$ maps every seed of length $n-\lambda(n)$ (truncated subtraction) to an $n$-bit string, $\lambda(n)=\lceil\log n\rceil+1$; reason: the type of the family; values off the domain are never used; the subtraction truncates only when $\lambda(n)>n$, where the source's type is undefined
--   - reading: Theorem 1.8 ("there is a family ... errs on at most $2^{-2\sqrt n}$ ... succeeds on less than $O(2^{-\sqrt n})$") → Corollary 6.7's explicit form for the family $C_s$, with the evaluability of Theorem 1.8 as item 1; reason: "Corollary 6.7 (Theorem 1.8, restated)", p.36
--   - reading: $A(C_s,w)$ → $A$ reads the index $s$; reason: $C_s$ is an indexed family (Theorem 1.8); a circuit description would contain $g_n$'s circuit, which need not be efficiently constructible, and the proof runs $A$ inside an NP/AM verifier given $s$
--   - reading: the demi-bits definition and "no $A$ ... with the following parameters" (stated for one $n$) → a verifier or algorithm must work for every sufficiently large $n$; reason: a uniform machine is asymptotic; Corollary 6.7 says "for every sufficiently large $n$"
--   - reading: "evaluable in space $O(s)$" → space $O(s(\sqrt N))=O(s(n))$ on indices of length $N=n^2$; reason: the "Observe" sentence of Corollary 6.7: evaluating $C_s$ costs computing $g$ plus $O(\log n)$ space
--   - reading: "computable in space $s(n)$" (no definition) → a machine given $n$ in binary and the seed prints $g_n$(seed) in work space $O(s(n))$; reason: the paper gives no definition; $g$ is indexed by $n$ because the seed length $n-\lceil\log n\rceil-1$ does not determine $n$
--   - encoding: $\log n$; $i$ in $\lceil\log n\rceil$ bits → `Real.logb 2`, `Nat.clog 2`; $i$ least significant bit first; reason: a fixed binary convention
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 1.8, p.5 (PDF p.7), and Corollary 6.7, pp.36–37 (PDF pp.38–39)

import Mathlib
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_demiCs
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSucc
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSound
import Definitions.Def_AvoidPlast_Supplement_IsRelaxedDemiBitsAM
import Definitions.Def_AvoidPlast_Supplement_ComputableInSpaceIdx

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 1.8 in the form of Corollary 6.7, average-case hardness for tiny-error
non-deterministic algorithms (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.5 and pp.36–37). Let `g = {g_n}`,
`g_n : {0,1}^{n - ⌈log n⌉ - 1} → {0,1}^n`, be a relaxed `1/4`-demi-bits generator against AM, and for
`s = (s_1, …, s_n) ∈ {0,1}^{n×n}` let `C_s(x, i) = g(x) ⊕ s_i` (`i` in `⌈log n⌉` bits, unused codes
mapped to `s_1`). Then

1. if `g` is computable in space `s(n) ≥ log n`, the family `{C_s}` indexed by `s` (of length
   `N = n²`) is evaluable in space `O(s(n))` (the "Observe" sentence of Corollary 6.7);
2. no non-deterministic polynomial-time machine `A` satisfies, for every sufficiently large `n`,
   `Pr_s[∃ w : A(C_s, w) ∈ {0,1}^n \ Range(C_s)] ≥ 3·2^{-n}` and
   `Pr_s[∀ w : A(C_s, w) ∉ Range(C_s)] ≥ 1 - 2^{-2n}`.

**Formalization Note** `A` reads the index `s`. The index has `N = n²` bits, so `2^{-2n}` and
`3·2^{-n}` are Theorem 1.8's `2^{-2√N}` and `O(2^{-√N})`; the evaluation space is stated as
`O(s(√N))`, the cost of computing `g` at output length `n`. -/
theorem theorem_1_8 (g : ℕ → List Bool → List Bool)
    (hg : ∀ n x, x.length = n - (Nat.clog 2 n + 1) → (g n x).length = n)
    (hdemi : IsRelaxedDemiBitsAM g (fun n => n - (Nat.clog 2 n + 1)) (fun _ => 1 / 4)) :
    (∀ sp : ℕ → ℝ, (∀ n : ℕ, Real.logb 2 n ≤ sp n) →
      ComputableInSpaceIdx g (fun n => n - (Nat.clog 2 n + 1)) sp →
      EvaluableInSpace
        (fun s z => demiCs g (fun n => Nat.clog 2 n + 1) (fun n => n) (Nat.sqrt s.length) s z)
        (fun N => Nat.sqrt N - 1) (fun N => Nat.sqrt N) (fun N => sp (Nat.sqrt N))) ∧
    ¬ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧ ∀ᶠ n : ℕ in Filter.atTop,
      3 * (2 : ℝ) ^ (-(n : ℝ)) ≤
        prob (n * n) (AvoidDemiSucc A a g (fun n => Nat.clog 2 n + 1) (fun n => n) n) ∧
      1 - (2 : ℝ) ^ (-(2 * n : ℝ)) ≤
        prob (n * n) (AvoidDemiSound A a g (fun n => Nat.clog 2 n + 1) (fun n => n) n) := by sorry

end AvoidPlast.Supplement
