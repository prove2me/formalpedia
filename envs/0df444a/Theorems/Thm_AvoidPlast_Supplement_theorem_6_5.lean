-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_6_5
-- name    : AvoidPlast.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:51:26.094212+00:00
-- url     : https://prove2.me/theorems/d62640c2-7e21-4931-b960-439a4c683ebf
-- title:
--   Theorem 6.5 — Ilango's hardness of Avoid for zero-error non-deterministic algorithms
-- statement:
--   For $t\in\mathbb N$, let $g=\{g_n:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n\}$ be an $\varepsilon$-demi-bits generator against $\mathsf{NP}$ with $\lambda(n)\ge\lceil\log t\rceil+130$, and for $s=(s_1,\dots,s_t)\in\{0,1\}^{t\times n}$ let $C_s(x,i)=g(x)\oplus s_i$. There is no non-deterministic polynomial-time machine $A$ (allowed to output $\bot$) that satisfies, for every sufficiently large $n$, over uniform $s$:
--
--   1. completeness: $\Pr_s[\exists w: A(C_s,w)\in\{0,1\}^n\setminus\mathrm{Range}(C_s)]\ge2^n\cdot\varepsilon(n)^t$;
--   2. soundness: $\Pr_s[\forall w: A(C_s,w)\notin\mathrm{Range}(C_s)]=1$.
--
--   The paper gives a new proof through the covering lemma (Lemma 6.4).
--
--   Differences from the source:
--   - encoding: $g:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n$ → `g : ℕ → List Bool → List Bool` with `hg`: $g_n$ maps every seed of length $n-\lambda(n)$ (truncated subtraction) to an $n$-bit string; reason: the type of the family; values off the domain are never used; the subtraction truncates only when $\lambda(n)>n$, where the source's type is undefined
--   - reading: $A(C_s,w)$ → $A$ reads the index $s$; reason: $C_s$ is an indexed family (Theorem 1.8); a circuit description would contain $g_n$'s circuit, which need not be efficiently constructible, and the proof runs $A$ inside an NP/AM verifier given $s$
--   - reading: the demi-bits definition and "no $A$ ... with the following parameters" (stated for one $n$) → a verifier or algorithm must work for every sufficiently large $n$; reason: a uniform machine is asymptotic; Corollary 6.7 says "for every sufficiently large $n$"
--   - reading: $\varepsilon$-demi-bits ($\varepsilon$ not said to be a constant or a function of $n$) → $\varepsilon:\mathbb N\to\mathbb R$, any function of $n$, no range constraint; reason: with $\varepsilon$ constant and $t$ fixed the threshold $2^n\varepsilon^t$ exceeds $1$ and the theorem is empty, so $\varepsilon$ depends on $n$; values outside $(0,1]$ make the demi-bits hypothesis false or the completeness threshold unattainable, so no range hypothesis is needed (trap 36)
--   - encoding: $i$ represented in $\lceil\log t\rceil$ bits (codes $\ge t$ not specified) → least significant bit first; codes $\ge t$ mapped to $s_1$; reason: the convention of Theorem 6.6; it does not change $\mathrm{Range}(C_s)$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.5, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSucc
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSound
import Definitions.Def_AvoidPlast_Supplement_IsDemiBitsNP

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 6.5, Ilango's result [Ila25, Theorem 3.3, Corollary 3.7] with a new proof (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
p.34). For `t ∈ ℕ`, let `g_n : {0,1}^{n - λ(n)} → {0,1}^n` be an `ε`-demi-bits generator against NP
with `λ(n) ≥ ⌈log t⌉ + 130`, and `C_s(x, i) = g(x) ⊕ s_i` for `s ∈ {0,1}^{t×n}`. No
non-deterministic polynomial-time `A` (allowed to output `⊥`) satisfies, for every sufficiently
large `n`, `Pr_s[∃ w : A(C_s, w) ∈ {0,1}^n \ Range(C_s)] ≥ 2^n·ε(n)^t` and
`Pr_s[∀ w : A(C_s, w) ∉ Range(C_s)] = 1`.

**Formalization Note** `ε` is a real function of `n` with no range constraint (for a constant
`ε < 1` the threshold `2^n ε^t` exceeds `1`; values outside `(0,1]` leave the statement true).
`A` reads the index `s`. -/
theorem theorem_6_5 (t : ℕ) (g : ℕ → List Bool → List Bool) (lam : ℕ → ℕ) (ε : ℕ → ℝ)
    (hg : ∀ n x, x.length = n - lam n → (g n x).length = n)
    (hdemi : IsDemiBitsNP g (fun n => n - lam n) ε)
    (hlam : ∀ n, Nat.clog 2 t + 130 ≤ lam n) :
    ¬ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ n * ε n ^ t ≤ prob (t * n) (AvoidDemiSucc A a g lam (fun _ => t) n) ∧
      prob (t * n) (AvoidDemiSound A a g lam (fun _ => t) n) = 1 := by sorry

end AvoidPlast.Supplement
