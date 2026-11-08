-- Prove2me | Theorems.Thm_AvoidPlast_universal_simulation
-- name    : AvoidPlast.universal_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:48:44.735122+00:00
-- url     : https://prove2.me/theorems/b8ca341d-5715-4de3-a06b-2b7d29bfca8d
-- title:
--   Proof of Theorem 5.14, (1)⇒(3): $U_\varepsilon$ simulates every low-space machine (corrected: $\gamma<\varepsilon^2$)
-- statement:
--   Let $\varepsilon\in(0,1)$, let $0<\gamma<\varepsilon^2$, and let $M$ be a deterministic machine of space $O(n^\gamma)$. For all sufficiently large $n$ there is a description $d$ of length $m_\varepsilon(n)=\lceil n^{\varepsilon^2}\rceil$ such that for every $x\in\{0,1\}^n$,
--
--   $$U_\varepsilon(x,d)=\begin{cases}M(x)&\text{if }|M(x)|=n,\\0^n&\text{otherwise.}\end{cases}$$
--
--   This is the universality of Definition 5.13, the step of the proof that turns a low-space machine into a description.
--
--   Differences from the source:
--   - correction: apply Item (1) with $\gamma=\varepsilon^2$ and state $U_\varepsilon(x,d_B)=M_B(x)$ → $\gamma<\varepsilon^2$; reason: with $\gamma=\varepsilon^2$ the step is false: with $m=\lceil n^{\varepsilon^2}\rceil$, the machine printing the first string $u0^{n-m-1}$, $u\in\{0,1\}^{m+1}$, that differs from every $U_\varepsilon(x,d)$ (one exists, as there are only $2^m$ descriptions) runs in space $O(n^{\varepsilon^2})$ by evaluating $U_\varepsilon$ bitwise (M3), and no $d$ gives $U_\varepsilon(x,d)$ equal to its output; Item (1) covers every $\gamma$, so the proof takes $\gamma<\varepsilon^2$
--   - encoding: $U_\varepsilon(x,d_B)=M_B(x)$ → $M(x)$ if it has $n$ bits and $0^n$ otherwise; reason: this is the page's own clause of Definition 5.13 on outputs of other length
--   - reading: fix a universal deterministic machine $U_\varepsilon$ with budgets $n^{\varepsilon^2}$ work space and $2^{n^{\varepsilon^2}}$ steps → the function $U_\varepsilon$ denoted by it: descriptions $0^j1e$, budgets $\lceil n^{\varepsilon^2}\rceil$ bits of simulation size and $2^{\lceil n^{\varepsilon^2}\rceil}$ steps; reason: the page leaves the universal machine open; the proof uses only universality and low-space evaluability, and the bit budget is what makes both true; reading R4
--   - encoding: space $n^\gamma$ (and evaluable in space $|x|^{\varepsilon^2}$) → work space at most $C(n^\gamma+1)$ for some $C$; reason: a strict bound fails at $n=0$ and for constants; with the exponent quantified the two forms agree; reading R2
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (1)⇒(3), p.29; Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_U

namespace AvoidPlast

/-- `U_ε` simulates every low-space machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (1)⇒(3), p.29, "For every
sufficiently large `n` we have `U_ε(x, d_B) = M_B(x)`"): for `ε ∈ (0,1)`, `0 < γ < ε²` and a machine of
space `O(n^γ)`, for all large `n` some description `d` of length `m_ε(n)` gives
`U_ε(x, d) = M(x)` on every `x ∈ {0,1}^n` where `M(x)` has `n` bits, and `0^n` otherwise.

**Formalization Note** The page takes `γ = ε²`, whose simulated time can exceed `2^{n^{ε²}}`; the
proof's own fix is `γ < ε²`. -/
theorem universal_simulation (ε γ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hγ : 0 < γ) (hγε : γ < ε ^ 2)
    (M : Machine 1) (hM : SpaceO M (fun n => (n : ℝ) ^ γ)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ d : List Bool, d.length = ceilPow (ε ^ 2) n ∧
      ∀ x : List Bool, x.length = n →
        U ε x d = if (output M ![x]).length = n then output M ![x]
          else List.replicate n false := by sorry

end AvoidPlast
