-- Prove2me | Theorems.Thm_BrouwerLaplacian_proof_lemma_5_5_N
-- name    : BrouwerLaplacian.proof_lemma_5_5_N
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:59:57.526182+00:00
-- url     : https://prove2.me/theorems/33b43323-a718-4cef-9f68-cb57b0b58414
-- title:
--   §5, proof of Lemma 5.5 — $N=CMC=C-2P$ and its spectrum (corrected: $\|N\|\le 1$; $=1$ for $n\ge 2$)
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$, let $M$ be its matrix ($M_{ii}=0$, $M_{ij}=P_{ii}+P_{jj}-2P_{ij}-1$ for $i\ne j$), let $C=I_n-\frac1nJ$, and let $N=CMC$. Then:
--
--   1. $N=C-2P$;
--   2. $N(Py)=-Py$ for every $y\in\mathbb R^n$ (eigenvalue $-1$ on $\operatorname{Im}P$);
--   3. $Nx=x$ for every $x$ with $\sum_i x_i=0$ and $Px=0$ (eigenvalue $1$ on $\mathbf 1^\perp\cap(\operatorname{Im}P)^\perp$);
--   4. $N\mathbf 1=0$ (eigenvalue $0$ on $\operatorname{span}\{\mathbf 1\}$);
--   5. the spectral norm satisfies $\|N\|\le 1$; and
--   6. $\|N\|=1$ whenever $n\ge 2$.
--
--   This step of the proof of Lemma 5.5 lets the trace duality $|\operatorname{tr}(AN)|\le\|A\|_*\|N\|$ turn Lemma 3.2 into the routing inequality.
--
--   **Formalization Note** $\|\cdot\|$ is the $\ell_2$ operator norm, the published `WainwrightHDS.NucNorm.opNorm2`. For symmetric $P$, $(\operatorname{Im}P)^\perp=\ker P$, so membership is written $Px=0$.
--
--   Differences from the source:
--   - correction: $\|N\|=1$ → $\|N\|\le 1$, and $\|N\|=1$ for $n\ge 2$; reason: at $n=1$, $k=0$, $P=(0)$ (an orthogonal projection of rank $0$ with $P\mathbf 1=0$) one has $C=(0)$ and $N=(0)$, so $\|N\|=0$; the proof uses only $\|N\|\le 1$ (p.7)
--   - encoding: $x\in(\operatorname{Im}P)^\perp$ → $Px=0$; reason: equal for symmetric $P$; same instances
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, §5, proof of Lemma 5.5, p.6

import Mathlib
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace BrouwerLaplacian

open Matrix

/-- **The matrix `N = CMC = C − 2P` and its norm (corrected: ‖N‖ ≤ 1; = 1 for n ≥ 2).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §5, proof of
Lemma 5.5, p.6: "Since M = d1ᵀ + 1dᵀ − 2P − J + I, and C1 = 0, CP = PC = P, we get
N = CMC = C − 2P. Thus N has eigenvalue −1 on Im P, eigenvalue 1 on 1⊥ ∩ (Im P)⊥, and
eigenvalue 0 on span{1}. In particular, ∥N∥ = 1."

Let `P` be an orthogonal projection of rank `k` with `P𝟙 = 0`, `M` its matrix (Lemma 5.3) and
`N = CMC`. Then (1) `N = C − 2P`; (2) `N(Py) = −Py` for every `y` (eigenvalue `−1` on `Im P`);
(3) `Nx = x` for every `x ⊥ 𝟙` with `Px = 0` (eigenvalue `1` on `𝟙⊥ ∩ (Im P)⊥`); (4) `N𝟙 = 0`;
(5) the spectral norm satisfies `‖N‖ ≤ 1`; and (6) `‖N‖ = 1` when `n ≥ 2`.

**Formalization Note.** `‖·‖` is the ℓ₂ operator norm `WainwrightHDS.NucNorm.opNorm2`.
`(Im P)⊥ = ker P` for symmetric `P`, so `x ∈ (Im P)⊥` is written `Px = 0`. The printed
"‖N‖ = 1" fails for `n = 1` (there `C = 0`, so `N = 0`); clauses (5)–(6) are the correction. -/
theorem proof_lemma_5_5_N {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    routingN P = centering n - 2 • P ∧
    (∀ y : Fin n → ℝ, routingN P *ᵥ (P *ᵥ y) = -(P *ᵥ y)) ∧
    (∀ x : Fin n → ℝ, ∑ i, x i = 0 → P *ᵥ x = 0 → routingN P *ᵥ x = x) ∧
    routingN P *ᵥ (fun _ => 1) = 0 ∧
    WainwrightHDS.NucNorm.opNorm2 (routingN P) ≤ 1 ∧
    (2 ≤ n → WainwrightHDS.NucNorm.opNorm2 (routingN P) = 1) := by sorry

end BrouwerLaplacian
