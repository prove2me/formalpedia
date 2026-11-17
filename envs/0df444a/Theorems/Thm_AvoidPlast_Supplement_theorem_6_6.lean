-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_6_6
-- name    : AvoidPlast.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:52:23.869605+00:00
-- url     : https://prove2.me/theorems/b339fd69-9b23-4034-acd9-d85320178727
-- title:
--   Theorem 6.6 — hardness of Avoid for non-deterministic algorithms that err
-- statement:
--   Let $g=\{g_n:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n\}$ be a relaxed $\varepsilon$-demi-bits generator against $\mathsf{AM}$, $t=t(n)$ polynomially bounded, $\kappa=\kappa(n)\in(0,1)$ and $\lambda(n)\ge\lceil\log t(n)\rceil+1$. For $s=(s_1,\dots,s_t)\in\{0,1\}^{t\times n}$ let $C_s(x,i)=g(x)\oplus s_i$, $i$ in $\lceil\log t\rceil$ bits with unused codes mapped to $s_1$. There is no non-deterministic polynomial-time machine $A$ (allowed to output $\bot$) that satisfies, for every sufficiently large $n$, over uniform $s$:
--
--   1. completeness: $\Pr_s[\exists w: A(C_s,w)\in\{0,1\}^n\setminus\mathrm{Range}(C_s)]\ge2^n\cdot2\kappa+2^n\cdot\varepsilon^t$;
--   2. soundness: $\Pr_s[\forall w: A(C_s,w)\notin\mathrm{Range}(C_s)]\ge1-\kappa$.
--
--   Corollary 6.7 (Theorem 1.8) is the case $\varepsilon=1/4$, $t(n)=n$, $\kappa(n)=2^{-2n}$.
--
--   Differences from the source:
--   - encoding: $g:\{0,1\}^{n-\lambda(n)}\to\{0,1\}^n$ → `g : ℕ → List Bool → List Bool` with `hg`: $g_n$ maps every seed of length $n-\lambda(n)$ (truncated subtraction) to an $n$-bit string; reason: the type of the family; values off the domain are never used; the subtraction truncates only when $\lambda(n)>n$, where the source's type is undefined
--   - reading: $A(C_s,w)$ → $A$ reads the index $s$; reason: $C_s$ is an indexed family (Theorem 1.8); a circuit description would contain $g_n$'s circuit, which need not be efficiently constructible, and the proof runs $A$ inside an NP/AM verifier given $s$
--   - reading: the demi-bits definition and "no $A$ ... with the following parameters" (stated for one $n$) → a verifier or algorithm must work for every sufficiently large $n$; reason: a uniform machine is asymptotic; Corollary 6.7 says "for every sufficiently large $n$"
--   - generalization: a relaxed $\varepsilon$-demi-bits generator, $\varepsilon$ a constant (Corollary 6.7 uses $\varepsilon=1/4$) → $\varepsilon:\mathbb N\to\mathbb R$, any function of $n$, no range constraint; reason: a constant $\varepsilon$ is a constant function, so the statement specializes to the source's; values outside $(0,1]$ make the demi-bits hypothesis false or the completeness threshold unattainable, so no range hypothesis is needed (trap 36)
--   - encoding: $t$ polynomially bounded → $t(n)\le b(n^b+1)$ for a constant $b$; reason: the usual meaning
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.6, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSucc
import Definitions.Def_AvoidPlast_Supplement_AvoidDemiSound
import Definitions.Def_AvoidPlast_Supplement_IsRelaxedDemiBitsAM

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 6.6, hardness of Avoid against non-deterministic algorithms that err (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.35).
Let `g_n : {0,1}^{n - λ(n)} → {0,1}^n` be a relaxed `ε`-demi-bits generator against AM, `t(n)`
polynomially bounded, `κ(n) ∈ (0,1)`, `λ(n) ≥ ⌈log t(n)⌉ + 1`, and `C_s(x, i) = g(x) ⊕ s_i` for
`s ∈ {0,1}^{t×n}` (`i` in `⌈log t⌉` bits, unused codes mapped to `s_1`). No non-deterministic
polynomial-time `A` (allowed to output `⊥`) satisfies, for every sufficiently large `n`,
`Pr_s[∃ w : A(C_s, w) ∈ {0,1}^n \ Range(C_s)] ≥ 2^n·2κ(n) + 2^n·ε(n)^{t(n)}` and
`Pr_s[∀ w : A(C_s, w) ∉ Range(C_s)] ≥ 1 - κ(n)`.

**Formalization Note** `A` reads the index `s`; `ε`, `κ`, `t` are functions of `n`; `ε` has no
range constraint (values outside `(0,1]` leave the statement true). -/
theorem theorem_6_6 (g : ℕ → List Bool → List Bool) (lam t : ℕ → ℕ) (ε κ : ℕ → ℝ)
    (hg : ∀ n x, x.length = n - lam n → (g n x).length = n)
    (hdemi : IsRelaxedDemiBitsAM g (fun n => n - lam n) ε)
    (ht : ∃ b : ℕ, ∀ n, t n ≤ b * (n ^ b + 1))
    (hκ : ∀ n, 0 < κ n ∧ κ n < 1)
    (hlam : ∀ n, Nat.clog 2 (t n) + 1 ≤ lam n) :
    ¬ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ n * (2 * κ n) + (2 : ℝ) ^ n * ε n ^ t n ≤
        prob (t n * n) (AvoidDemiSucc A a g lam t n) ∧
      1 - κ n ≤ prob (t n * n) (AvoidDemiSound A a g lam t n) := by sorry

end AvoidPlast.Supplement
