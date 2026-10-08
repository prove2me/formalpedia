-- Prove2me | Theorems.Thm_ErschlerZheng_orbitKernel_upsilon_eq_and_boundarySize_ge
-- name    : ErschlerZheng.orbitKernel_upsilon_eq_and_boundarySize_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T06:52:27.975058+00:00
-- url     : https://prove2.me/theorems/9d959120-f41b-4efb-aee1-92d8d7a0bcec
-- title:
--   p. 48 — on level n, υ_n induces the same kernel as u_{F_n}; and for U ⊂ 1^∞·G with |U| ⩽ 2^{n−1}, the kernel of ½(υ_n + υ̌_n) has |∂U|/|U| ⩾ 1/2
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $n \ge 1$ be divisible by $D$. Then:
--
--   1. on the orbit of the vertex $1^n$, the transition kernel induced by $\upsilon_n$ (`orbitKernel … (upsilon …) (List.replicate n true)`) equals the one induced by the uniform measure on the $n$-quasi-cubic set $F_n = \{g_n^{\epsilon_n} \cdots g_1^{\epsilon_1} : \epsilon_i \in \{0, 1\}\}$ of $(g_n)$ (`uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n)`);
--   2. on the level $\mathsf L_n$: for all words $x, y$ of length $n$, $\sum_{g \in G_\omega,\ x \cdot g = y} \upsilon_n(g) = \sum_{g \in G_\omega,\ x \cdot g = y} \mathbf u_{F_n}(g)$;
--   3. for the kernel $P_n$ induced on the orbit $1^\infty \cdot G_\omega$ by $\frac12(\upsilon_n + \check\upsilon_n)$ (`upsilonCheck`), every non-empty finite set $U$ of the orbit with $|U| \le 2^{n-1}$ satisfies $|\partial_{P_n}U|/|U| \ge \frac12$, where $|\partial_{P_n}U| = \sum_{x \in U}\sum_{y \notin U} P_n(x, y)$ (`MarkovChain.boundarySize` with the counting measure).
--
--   Erschler and Zheng, p. 48: “The following on-diagonal upper bound does not depend on the choice of $(k_n)$ because by construction, on the finite level $\mathsf L_n$ the transition kernel induced by $\upsilon_n$ coincide with the one induced by $\mathbf u_{F_n}$.” and, in the proof of Proposition 7.19, “Let $P_n$ be the transition kernel on the orbit of $o$ induced by $\frac12(\upsilon_n + \check\upsilon_n)$. As in the proof of Lemma 5.2, from Lemma 7.15 we derive that for a set $U \subset o \cdot G_\omega$ with volume $|U| \leqslant 2^{n-1}$, $\frac{|\partial_{P_n}U|}{|U|} \geqslant \frac12$.”
--
--   “On the finite level $\mathsf L_n$” is conjunct 2, the kernels compared word by word on $\mathsf L_n$; conjunct 1 is the same comparison stated for the kernels `orbitKernel` induces on the orbit of $1^n$, and that orbit is all of $\mathsf L_n$, since $G_\omega$ acts transitively on each level ([`ErschlerZheng.isLevelTransitive_and_isotropy_grigorchuk`](https://prove2.me/theorems/fe323b70-1820-433c-aafb-4eef25a952b9)). $F_n$ is the quasi-cubic set of Proposition 5.4 (p. 26) for $(g_n)$ with parameters $k_j = 1$; it is the paper's $F_n$ of §5. $U$ is taken finite and non-empty, as the ratio requires, and $o = 1^\infty$. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 48, the kernel of υ_n on level n and its isoperimetry

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_MarkovChain_HeatKernels
open scoped RightActions

namespace ErschlerZheng

theorem orbitKernel_upsilon_eq_and_boundarySize_ge (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) :
    orbitKernel (grigorchuk ω) (fun g => upsilon D ω k n g) (List.replicate n true) =
      orbitKernel (grigorchuk ω)
        (fun g =>
          uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut))
        (List.replicate n true) ∧
    (∀ x y : List Bool, x.length = n → y.length = n →
      ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then upsilon D ω k n g else 0) =
        ∑' g : grigorchuk ω, (if x <• (g : Garrido.BinaryTreeAut) = y then
          uniformMeasure (quasiCubicSet (seqG ω) (fun _ => 1) n) (g : Garrido.BinaryTreeAut)
          else 0)) ∧
    ∀ U : Finset (orbitOne ω), U.Nonempty → U.card ≤ 2 ^ (n - 1) →
      (1 : ℝ) / 2 ≤
        MarkovChain.boundarySize
          (orbitKernel (grigorchuk ω) (fun g => (upsilon D ω k n g + upsilonCheck D ω k n g) / 2)
            oneRay) (fun _ => 1) U / U.card := by
  sorry

end ErschlerZheng
