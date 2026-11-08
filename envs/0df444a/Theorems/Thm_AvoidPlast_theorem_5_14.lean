-- Prove2me | Theorems.Thm_AvoidPlast_theorem_5_14
-- name    : AvoidPlast.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:00.743227+00:00
-- url     : https://prove2.me/theorems/270c427b-a9f5-40f6-8c2d-7c7244ba0539
-- title:
--   Theorem 5.14 — under prBP$^*$L = prL, FP in space $n^\gamma$ on average, low-space Avoid hardness and diagonalization hardness are equivalent
-- statement:
--   Assume that $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$. Then the following are equivalent:
--
--   1. For every $f\in\mathrm{FP}$ and every constant $\gamma>0$, there is a deterministic space-$n^\gamma$ machine $M_f$ such that, for every sufficiently large $n$,
--   $$\Pr_{x\in\{0,1\}^n}[M_f(x)=f(x)]\ge1-n^{-\omega(1)}.$$
--   2. Assumption 1.1 holds with $p(n)=n^{-\omega(1)}$: for every sufficiently small constant $\varepsilon>0$ there is a family of Avoid instances $C=\{C_x\}$ stretching $|x|^{\varepsilon^2}$ bits to $|x|^\varepsilon$ bits and evaluable in space $|x|^{\varepsilon^2}$ such that every polynomial-time algorithm solves Avoid$(C_x)$ on at most a $p(n)$ fraction of the $n$-bit $x$, for all large $n$.
--   3. For every constant $\varepsilon\in(0,1)$ and every deterministic polynomial-time machine $B$, for every sufficiently large $n$,
--   $$\Pr_{x\in\{0,1\}^n}[B(x)\in\mathrm{Diag}_\varepsilon(x)]\le n^{-\omega(1)}.$$
--
--   This is the general form of Theorem 1.2 of the paper: trading time for space in the deterministic simulation of polynomial time is equivalent to the average-case hardness of low-space range avoidance.
--
--   **Formalization Note** Theorem 1.2's wording of item 1 (for all $n$) is equivalent to the wording here: $\nu$ can be raised to $1$ on the finitely many small $n$.
--
--   Differences from the source:
--   - encoding: $n^{-\omega(1)}$ → an existential negligible $\nu$ (the published `QuantumPRC.Negligible`: for every real $c>0$, eventually $|\nu(n)|<n^{-c}$); reason: the standard meaning; reading R1 of the paper notes
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
--   - encoding: stretching $|x|^{\varepsilon^2}$ bits to $|x|^{\varepsilon}$ bits → lengths $\lceil n^{\varepsilon^2}\rceil$ and $\lceil n^{\varepsilon}\rceil$; reason: bit lengths are integers; matches $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$ of Definition 5.13; reading R3
--   - reading: fix a universal deterministic machine $U_\varepsilon$ with budgets $n^{\varepsilon^2}$ work space and $2^{n^{\varepsilon^2}}$ steps → the function $U_\varepsilon$ denoted by it: descriptions $0^j1e$, budgets $\lceil n^{\varepsilon^2}\rceil$ bits of simulation size and $2^{\lceil n^{\varepsilon^2}\rceil}$ steps; reason: the page leaves the universal machine open; the proof uses only universality and low-space evaluability, and the bit budget is what makes both true; reading R4
--   - reading: the machine model is the RAM model (p.13), unspecified → a multitape machine with read-only input tapes, each accessed by head moves and index jumps, a fixed work alphabet and a write-only output; reason: the page does not fix a RAM; FP and space $n^\gamma$ are robust under the choice, and sublinear time needs the random access; reading R5
--   - encoding: indexed family of circuits $C[\ell_{in}\to\ell_{out},s]$ with $s$ arbitrary → a map $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$; reason: every such map has a circuit and the size is unconstrained; reading R8
--   - encoding: persistent two-way read-only random tape of unstated length → a random string of the fixed length of the machine's time bound, $C(n^C+1)$, with a head that may also jump; reason: a free length function would be non-uniform advice and would make $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$ false; a jump is simulated by a walk within polynomial time and logspace
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, p.29; Theorem 1.2, p.3

import Mathlib
import Definitions.Def_AvoidPlast_PrBPstarLEqPrL
import Definitions.Def_AvoidPlast_Assumption11
import Definitions.Def_AvoidPlast_LowSpaceFP
import Definitions.Def_AvoidPlast_DiagHard

namespace AvoidPlast

/-- Theorem 5.14, the general form of Theorem 1.2 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.29; p.3). Assume `prBP*L = prL`. Then the
following are equivalent:

1. `LowSpaceFP`: for every `f ∈ FP` and every `γ > 0` there is a deterministic space-`n^γ` machine `M_f`
   such that, for every sufficiently large `n`, `Pr_x[M_f(x) = f(x)] ≥ 1 - n^{-ω(1)}`;
2. `Assumption11`: Assumption 1.1 holds with `p(n) = n^{-ω(1)}`;
3. `DiagHard`: for every `ε ∈ (0,1)` and every deterministic polynomial-time machine `B`, for every
   sufficiently large `n`, `Pr_x[B(x) ∈ Diag_ε(x)] ≤ n^{-ω(1)}`. -/
theorem theorem_5_14 (hyp : PrBPstarLEqPrL) :
    List.TFAE [LowSpaceFP, Assumption11, DiagHard] := by sorry

end AvoidPlast
