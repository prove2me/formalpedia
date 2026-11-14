-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedClock_rounded_families
-- name    : ConsistentSubmodular.ProtectedClock.rounded_families
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:32.217192+00:00
-- url     : https://prove2.me/theorems/24dd7c05-015e-4cc1-9bb3-ecb500a07718
-- title:
--   Rounded window families and bridges from rounded windows and pure-endpoint bridges
-- statement:
--   Let $C$ be a protected clock $(F,\eta,b,\ell)$, $f$ an objective on $[n]$, $\kappa\in\mathbb N$, $O$ a certificate family (level $O.\mathrm{level}$), $N\ge200$, and $H_W,L_W,H_B,L_B,B,L\in\mathbb N$ with $L_W\le L$, $L_B\le L$ and
--   $$\kappa+\kappa/N+H_W\le B,\qquad \kappa+\kappa/N+H_B\le B .$$
--   Write $\alpha'=O.\mathrm{level}-2/N$. Assume that
--
--   - for every $i$ a rounded window $R_i$ of the fractional window $C.\mathrm{fractionalWindows}\,f\,\kappa\,O\,N\,i$ is given, with forced reserve $H_W$ and length coefficient $L_W$;
--   - for every $i$ there is an operation path $P$ (steps changing one element at a time) with $P_0=$ the window terminal set of window $i$, $P_{|P|}=$ the initial set of window $i+1$, length $|P|\le L_B\kappa$, and for all $j$: $P_j\subseteq$ (terminal of window $i$) $\cup$ (initial of window $i+1$), $|P_j|\le\kappa+\kappa/N+H_B$, and
--   $$\alpha'\cdot\mathrm{OPT}_\kappa\big(C.\mathrm{start}(i+1)\big)\ \le\ f\big(\mathrm{Buf}_i\cup P_j\big),$$
--   where $\mathrm{Buf}_i$ is the buffer of elements arriving during window $i$.
--
--   Then there exists a rounded window family $W$ for $(f,\kappa,\alpha',C,B,L)$ such that a rounded bridge family for $W$ exists.
--
--   This assembles the independently rounded windows and their pure-endpoint bridges into the family required by the global schedule; all comparisons use the actual prefix optimum at the corresponding clock time.
--
--   **Formalization Note**: Divisions $\kappa/N$ and $2/N$ are real divisions; the hypothesis $N\ge200$ is only used to make $N>0$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ClockRounded.lean#L19-L86 (`ConsistentSubmodular.ProtectedClock.rounded_families`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ) (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N)
variable (HW LW HB LB B L : ℕ)

theorem ConsistentSubmodular.ProtectedClock.rounded_families
    (R : ∀ i, RoundedWindow (C.fractionalWindows f κ O N (by omega) i) HW LW)
    (hcardW : (κ : ℝ) + κ / N + HW ≤ B) (hcardB : (κ : ℝ) + κ / N + HB ≤ B)
    (hLW : LW ≤ L) (hLB : LB ≤ L)
    (bridges : ∀ i, ∃ P : SetOperationPath n,
      P.node 0 = C.windowTerminal f κ i ∧ P.node P.length = C.windowInitial f κ (i + 1) ∧
      P.length ≤ LB * κ ∧ ∀ j, P.node j ⊆ C.windowTerminal f κ i ∪ C.windowInitial f κ (i + 1) ∧
        ((P.node j).card : ℝ) ≤ κ + κ / N + HB ∧
        (O.level - 2 / N) * f.prefixOptimum κ (C.start (i + 1)) ≤
          f.value (C.windowBuffer n i (C.windowDuration i) ∪ P.node j)) :
    ∃ W : RoundedWindowFamily f κ (O.level - 2 * ((1 : ℝ) / N)) C B L,
      Nonempty (RoundedBridgeFamily W) := by sorry
