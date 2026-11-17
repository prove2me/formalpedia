-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_11
-- name    : AvoidPlast.Supplement.theorem_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:49:49.32784+00:00
-- url     : https://prove2.me/theorems/00183556-9d98-4d51-92c4-7c297cdb79b9
-- title:
--   Theorem 5.11 — worst-case simulation of E with alternations
-- statement:
--   If every $L\in\mathsf P$ has $k=k_L$ and a linear-time $\Sigma_k$ machine that decides $L$ correctly on at least $.999$ of the $n$-bit inputs, then
--   $$\mathsf E\subseteq\bigcap_{\varepsilon>0}\bigcup_{k\in\mathbb N}\Sigma_k\mathrm{TIME}[2^{\varepsilon n}].$$
--
--   Differences from the source:
--   - reading: "decides $L$ correctly on at least $.999$ of the $n$-bit inputs" (no quantifier on $n$) → for every sufficiently large $n$; reason: the weaker hypothesis, so the stronger theorem; finitely many lengths can be corrected
--   - encoding: $\Sigma_k\mathrm{TIME}[2^{\varepsilon n}]$ → time $O(\lceil2^{\varepsilon n}\rceil)$; reason: time bounds are natural numbers
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.11, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_InE
import Definitions.Def_AvoidPlast_Supplement_IsSigmaMachine
import Definitions.Def_AvoidPlast_Supplement_sigmaAccepts
import Definitions.Def_AvoidPlast_Supplement_InSigmaTIME

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.11, worst-case simulation of E in small time with alternations (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.27). If
every `L ∈ P` has `k = k_L` and a linear-time `Σ_k` machine deciding `L` correctly on at least
`.999` of the `n`-bit inputs, then `E ⊆ ∩_{ε>0} ∪_k Σ_kTIME[2^{εn}]`.

**Formalization Note** The hypothesis is required for every sufficiently large `n` (the source does
not say; a linear-time `Σ_k` machine can be patched on finitely many lengths). -/
theorem theorem_5_11
    (h : ∀ L : Set (List Bool), InP L → ∃ (k : ℕ) (V : Machine (k + 1)) (C : ℕ),
      IsSigmaMachine k V (fun n => n) C ∧ ∀ᶠ n : ℕ in Filter.atTop,
        (0.999 : ℝ) ≤ prob n (fun x => sigmaAccepts k V (fun n => n) C x ↔ x ∈ L)) :
    ∀ L : Set (List Bool), InE L → ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, InSigmaTIME k (fun n => ⌈(2 : ℝ) ^ (ε * n)⌉₊) L := by sorry

end AvoidPlast.Supplement
