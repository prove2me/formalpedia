-- Prove2me | Theorems.Thm_BC1992_lemma_2_2_polytime_soundness
-- name    : BC1992.lemma_2_2_polytime_soundness
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T00:36:57.550207+00:00
-- url     : https://prove2.me/theorems/32d5655e-2a5c-4608-bf1f-83fac502d3f0
-- title:
--   Lemma 2.2: Frame-Preserving Compilation of BC Programs and Polynomial-Time Soundness (BC <= FP)
-- statement:
--   Establishes Lemma 2.2 of Bellantoni and Cook (1992):
--
--   1. For every program $f : \mathsf{Fn}\;n\;m$, frame base $\mathit{base}$, normal arguments $\mathit{xs}$ ($|\mathit{xs}| = n$), and safe arguments $\mathit{ys}$ ($|\mathit{ys}| = m$) with all word lengths bounded by $K$ and empty scratch stacks $\ge \mathit{base}$, $\mathsf{compileBC}\;\mathit{base}\;f$ evaluates $f.\mathsf{eval}\;\mathit{xs}\;\mathit{ys}$ into stack $\mathit{base}$ within $f.\mathsf{timePoly}.\mathsf{eval}\;K$ steps while preserving all argument stacks and clearing all workspace stacks above the frame.
--   2. For every closed unary program $\mathit{prog} : \mathsf{Fn}\;1\;0$ and input $x : \mathsf{Word}$, the compiled multi-tape Turing machine $\mathsf{stmtToTM}\;(\mathsf{topCompileBC}\;\mathit{prog})$ halts on $x$ within $(\mathsf{topTimePoly}\;\mathit{prog}).\mathsf{eval}\;|x|$ transitions with output $\mathit{prog}.\mathsf{eval}\;[x]\;[]$.
--   3. Consequently, every $\mathsf{BC}$-definable unary word function belongs to $\mathsf{FP}$ ($\mathsf{BCDefinable}(f) \implies \mathsf{FP}(f)$).
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 2, Lemma 2.2, pp. 101-102.

import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines

namespace BC1992

/-- **Lemma 2.2 (Bellantoni & Cook 1992 — Polynomial-Time Soundness, `BCDefinable f → FP f`)**:
    1. (`exec_compileBC`) For every `f : Fn n m`, frame base `base`, stack state `σ`,
       normal arguments `xs` (`xs.length = n`), and safe arguments `ys` (`ys.length = m`)
       with all word lengths bounded by `K` and `∀ r ≥ base, σ r = []`, `compileBC base f`
       executes from `setFrame σ (base + 1) (xs ++ ys)` to
       `(setFrame σ (base + 1) (xs ++ ys)).set base (f.eval xs ys)` in `c ≤ f.timePoly.eval K` steps.
    2. (`topCompileBC_haltsWithin`) For every closed unary program `prog : Fn 1 0` and input `x : Word`,
       `stmtToTM (topCompileBC prog)` halts on `x` within `(topTimePoly prog).eval x.length` steps
       with output `prog.eval [x] []`.
    3. (`bc_soundness`) Every BC-definable word function `f : Word → Word` is in `FP`. -/
theorem lemma_2_2_polytime_soundness :
    (∀ {n m : Nat} (f : Fn n m) (base : Nat) (σ : Stacks)
       (xs ys : List Word) (K : Nat),
      xs.length = n →
      ys.length = m →
      (∀ r : Nat, base ≤ r → σ r = []) →
      (∀ x ∈ xs, x.length ≤ K) →
      (∀ y ∈ ys, y.length ≤ K) →
      ∃ c : Nat,
        c ≤ f.timePoly.eval K ∧
        Exec (compileBC base f)
          (setFrame σ (base + 1) (xs ++ ys))
          c
          ((setFrame σ (base + 1) (xs ++ ys)).set base (f.eval xs ys))) ∧
    (∀ (prog : Fn 1 0) (x : Word),
      (stmtToTM (topCompileBC prog)).HaltsWithin x
        ((topTimePoly prog).eval x.length)
        (prog.eval [x] [])) ∧
    (∀ (f : Word → Word), BCDefinable f → FP f) := by
  sorry

end BC1992
