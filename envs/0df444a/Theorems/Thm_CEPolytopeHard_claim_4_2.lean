-- Prove2me | Theorems.Thm_CEPolytopeHard_claim_4_2
-- name    : CEPolytopeHard.claim_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:12.521373+00:00
-- url     : https://prove2.me/theorems/bca2269d-bc4d-4d8e-a1c1-b14f18b0e92a
-- title:
--   Claim 4.2 — extracting a fixed point from a $\zeta$-convex EFP of the lift
-- statement:
--   Let $f$ map $[0,1]^d$ into itself and be $L$-Lipschitz there in the normalized norm, with $L \ge 1$; let $0 < \delta \le 1$, $\lambda \in \mathbb R$ and an integer $K \ge 2$, and let $r$, $b$, the lift $g$ and $\zeta = \delta/(16 r b^r)$ be as in (12). If $\mu$ is a distribution on $[0,1]^{dr}$ with at most $K$ support points and
--   $$
--   \mathbb E_{x\sim\mu}[Q(x) - Q(g(x))] \le \zeta \quad \text{for every convex 1-Lipschitz } Q,
--   $$
--   then some $x \in \operatorname{supp}\mu$ and some layer $\ell \in [r]$ satisfy
--   $$
--   \|f(x^{(\ell)}) - x^{(\ell)}\|_2 \le \delta .
--   $$
--
--   This is the quantitative form of the paper's Theorem 1 argument, specialized to the parameters (12) of Section 4.
--
--   Differences from the source:
--   - generalization: f the polynomial circuit map of p.20 with L = 3λ → any f mapping [0, 1]^d into itself, L-Lipschitz in the normalized norm with L ≥ 1, and any real λ in b; reason: the Section 3.2 argument uses only these properties of f, and b only needs b ≥ max{2, 2^{14}(L + 1)²/δ³}
--   - encoding: layers ℓ ∈ [r]; ⌈log₂ K⌉ → 0-based layers with weight b^{−(ℓ+1)}; Nat.clog 2 K; reason: Lean indexing; same lift
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Claim 4.2 and Eq. (12), p.21

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsConvexEFP
import Definitions.Def_CEPolytopeHard_liftG

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Claim 4.2 (extracting a fixed point)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.21: "if K ≥ 2 is the support, we set
r := (1 + ⌈log₂ K⌉)⌈128(L + 1)²/δ²⌉ and b := ⌈max{2, 2λ + 1, 2^{14}(L + 1)²/δ³}⌉, (12) and define
g : [0, 1]^{dr} → [0, 1]^{dr} by g(x^{(1)}, . . . , x^{(r)}) = ((1 − b^{−ℓ})x^{(ℓ)} + b^{−ℓ}f(x^{(ℓ)}))_{ℓ=1}^r.
Moreover, ζ := δ/(16rb^r). … Claim 4.2 (Extracting a fixed point). If μ has support size at most
K and satisfies E[Q(x) − Q(g(x))] ≤ ζ for every convex 1-Lipschitz Q, then some x ∈ supp μ and
ℓ ∈ [r] satisfy ∥f(x^{(ℓ)}) − x^{(ℓ)}∥₂ ≤ δ").

Let `f` map `[0, 1]^d` into itself and be `L`-Lipschitz there in the normalized norm, `L ≥ 1`;
let `0 < δ ≤ 1`, `λ ∈ ℝ`, an integer `K ≥ 2`, and `r`, `b`, `g`, `ζ` as in (12). Every
distribution `μ` on `[0, 1]^{dr}` with at most `K` support points that is a `ζ`-convex EFP of `g`
has a support point `x` and a layer `ℓ` with `‖f(x^{(ℓ)}) − x^{(ℓ)}‖₂ ≤ δ`.

**Formalization Note** In the paper `f` is the circuit map of p.20 (`L = 3λ`); here `f` is any map
with the properties the Section 3.2 argument uses, and `λ` (which enters only through `b`) is
arbitrary. Layers are 0-based (`liftG`), `⌈log₂ K⌉` is `Nat.clog 2 K`, and norms are normalized
(p.9), in dimension `dr` for `g` and `d` for a layer. -/
theorem claim_4_2 {d : ℕ} (f : (Fin d → ℝ) → Fin d → ℝ)
    (hf : ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, f x ∈ Set.Icc (0 : Fin d → ℝ) 1) (L : ℝ) (hL : 1 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin d → ℝ) 1,
      nnorm (f x - f y) ≤ L * nnorm (x - y))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (lam : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (μ : (Fin (liftR K L δ) × Fin d → ℝ) →₀ ℝ) (hsupp : μ.support.card ≤ K)
    (hμ : IsConvexEFP (Set.Icc (0 : Fin (liftR K L δ) × Fin d → ℝ) 1) (liftG (liftB lam L δ) f)
      (liftZeta (liftR K L δ) (liftB lam L δ) δ) μ) :
    ∃ x ∈ μ.support, ∃ ℓ : Fin (liftR K L δ), nnorm (f (layer x ℓ) - layer x ℓ) ≤ δ := by sorry

end CEPolytopeHard
