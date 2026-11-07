-- Prove2me | Theorems.Thm_DetANN_mgg_spectral_bound
-- name    : DetANN.mgg_spectral_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:27.763824+00:00
-- url     : https://prove2.me/theorems/def8c076-a87c-4a56-a000-e58e433e39ce
-- title:
--   Appendix B, p.20 — the Margulis–Gabber–Galil graph on $\mathbb Z_m^2$ is undirected with $\|W_m|_{\mathbf 1^\perp}\|\le5\sqrt2/8$
-- statement:
--   For every integer $m\ge1$, the Margulis–Gabber–Galil graph on $\mathbb Z_m^2$, with the eight neighbor occurrences $(x\pm2y,y)$, $(x\pm(2y+1),y)$, $(x,y\pm2x)$, $(x,y\pm(2x+1))$ (arithmetic modulo $m$), is undirected and $8$-regular, and its normalized adjacency matrix $W_m$ satisfies
--
--   $$\|W_mf\|_2\le\frac{5\sqrt2}{8}\|f\|_2\qquad\text{for every }f:\mathbb Z_m^2\to\mathbb R\text{ with }\sum f=0 .$$
--
--   This is the explicit constant-degree expander behind Lemma 7.1, a cited result of Gabber and Galil.
--
--   Differences from the source:
--   - generalization: the bound for m a power of two (the only case the paper uses) → every m ≥ 1; reason: the cited theorem holds for every m; powers of two are a special case
--   - encoding: ‖W_m restricted to 1^⊥‖_{2→2} ≤ 5√2/8 → Σ_u (W_m f)_u² ≤ (5√2/8)² Σ f² for every mean-zero f; reason: the operator norm on 1^⊥ is the best such constant; the squared form is equivalent
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Appendix B, p.20 (PDF p.20); [GG81], [HLW06, §8, Thm 8.1]

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_MGG

namespace DetANN

/-- **The Margulis–Gabber–Galil bound** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Appendix B, p.20; [GG81], [HLW06, §8]).
For every `m ≥ 1`, the 8-regular Margulis–Gabber–Galil multigraph on `ℤ_m²` is undirected and its
normalized adjacency matrix `W_m` satisfies `‖W_m f‖ ≤ (5√2/8)‖f‖` for every mean-zero `f`.

**Formalization Note.** `m ≥ 1` is the instance `NeZero m` (`ZMod 0 = ℤ` is infinite). The paper uses
the bound only for `m` a power of two; this is the cited result for every `m`. The spectral bound
is stated squared (`DetANN.ContractsMeanZero`). -/
theorem mgg_spectral_bound (m : ℕ) [NeZero m] :
    IsUndirected (mggNbr m) ∧ ContractsMeanZero (adjMatrix (mggNbr m)) theta0 := by sorry

end DetANN
