-- Prove2me | Theorems.Thm_AvoidPlast_augmented_pcp
-- name    : AvoidPlast.augmented_pcp
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:12.832862+00:00
-- url     : https://prove2.me/theorems/1f5059a0-a3df-4a58-a149-fbc2e0837ece
-- title:
--   Proof of Theorem 5.14, (2)⇒(1): an augmented PCP for $L_{pad}$ that reveals $f(x)$
-- statement:
--   Let $F$ compute $f$ in time $O(n^k)$ with $k\ge1$, and let $\alpha\in(0,1)$ be rational. Then $L_{pad}=\{xy:|y|=\lceil|x|^{k/\alpha}\rceil\}\in\mathrm{DTIME}[N^\alpha]$, and there is a PCP system for $L_{pad}$ with perfect completeness, the soundness of Theorem 4.1, non-adaptive $\mathrm{polylog}(N)$ queries, $\mathrm{polylog}(N)$ space and proof length at most $N^{c_0\alpha}$ for a universal $c_0$, such that any proof of $xy$ accepted for every verifier random string reveals $f(x)$: a logspace machine reading $xy$ and the proof prints $F(x)$. This is the proof containing the output, which Theorem 5.12 then prints.
--
--   Differences from the source:
--   - reading: if a proof is accepted for every verifier random string, then $\tau$ contains $f(x)$ → a logspace machine $E$ on $(xy,\pi)$ prints $F(x)$; reason: the proof of the goal needs a low-space way to read $f(x)$ off the printed proof, and $\tau$ is a tableau, whose last row a logspace machine reads
--   - reading: $L_{pad}=\{(x,y):x\in L\wedge|x|\le|(x,y)|^{\alpha/k}\}$, with $\alpha$ a sufficiently small constant → the strings $xy$ with $|y|=\lceil|x|^{k/\alpha}\rceil$, $\alpha$ rational; reason: the printed condition with a plain string does not determine the split, the page uses exactly these lengths ("Let $\ell=\lceil n^{k/\alpha}\rceil$ and $N=n+\ell$") and a computable $\alpha$ is needed to decide the lengths; the page chooses $\alpha$ freely
--   - encoding: $F$ runs in time $n^k$ → time $C(n^k+1)$; reason: so that small $n$ are not excluded
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (2)⇒(1), p.30

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_PCPSystem
import Definitions.Def_AvoidPlast_IsPCPSystem
import Definitions.Def_AvoidPlast_IsQuasiBounded
import Definitions.Def_AvoidPlast_padLen
import Definitions.Def_AvoidPlast_Lpad

namespace AvoidPlast

/-- The augmented PCP for `L_pad` that reveals `f(x)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (2)⇒(1), p.30). Let
`F` run in time `O(n^k)` and let `α ∈ (0,1)` be rational. Then `L_pad ∈ DTIME[N^α]`, and there is a PCP
system for it with the conclusions of Theorem 4.1 at `ε = α` and proof length `≤ N^{c₀α}`, for a universal
`c₀`, together with a logspace machine `E` that reads `F(x)` off any proof of `xy` accepted for every
random string.

**Formalization Note** "`τ` contains `f(x)`" is the extraction machine `E`. `α` is rational so that the
padding length is computable; the page chooses `α` freely. -/
theorem augmented_pcp : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (F : Machine 1) (C k : ℕ), 1 ≤ k →
    (∀ x : List Bool, HaltsWithin F ![x] (C * (x.length ^ k + 1))) →
    ∀ α : ℚ, 0 < α → α < 1 → ∀ s : ℕ → ℝ, IsQuasiBounded s →
      ∃ (V₀ : Machine 2) (C₀ : ℕ) (S : PCPSystem) (E : Machine 2) (a : ℕ),
        IsNTimeVerifier V₀ (Lpad k α) (ceilPow α) C₀ ∧
        (∀ z ∈ Lpad k α, Accepts V₀ ![z, []]) ∧
        IsPCPSystem S (Lpad k α) V₀ (ceilPow α) C₀ s ∧
        (∀ᶠ N : ℕ in Filter.atTop, (S.proofLen N : ℝ) ≤ (N : ℝ) ^ (c₀ * (α : ℝ))) ∧
        ∀ (x y π : List Bool), y.length = padLen k α x.length →
          π.length = S.proofLen (x ++ y).length →
          (∀ ρ : List Bool, ρ.length = S.randLen (x ++ y).length →
            Accepts S.V ![x ++ y, ρ, π]) →
          Halts E ![x ++ y, π] ∧ output E ![x ++ y, π] = output F ![x] ∧
            (workSpace E ![x ++ y, π] : ℝ) ≤ a * (lg (x ++ y).length + 1) := by sorry

end AvoidPlast
