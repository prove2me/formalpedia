-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_polynomial_kernel
-- name    : DenseProdQSAT.Testing.polynomial_kernel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:03.607807+00:00
-- url     : https://prove2.me/theorems/4ca59e25-4d7f-4905-afc5-83eb1e9ff4c5
-- title:
--   Lemma 4.10 — uniform polynomial kernel representation
-- statement:
--   Fix $n,d\ge1$, $k\ge2$, a quantum instance $\Phi$, a support $F$, and $X\subseteq V\setminus F$ with $1\le|X|\le k-1$. There is one polynomial matrix family $M_{F,X}$, chosen before the amplitudes on $F$, with exactly $d^{|X|}$ columns. Every entry is homogeneous of some degree at most $k$ in the $2d|F|$ real and imaginary local amplitudes. For every normalized assignment $\psi$ satisfying the constraints within $F$,
--
--   $$L_{(F,\psi)}(X)=\ker M_{F,X}(\operatorname{Re}\psi,\operatorname{Im}\psi).$$
--
--   Coefficients may depend on the instance, $F$, and $X$. Entry degrees can differ. The matrix acts complex linearly on vectors on $X$. This is the algebraic representation needed for the potential approximation and the intermediate growth bound.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
--   - reading: matrix notation after fixing A with entries polynomial in its amplitudes → one polynomial matrix for each instance, support F and X, evaluated at every admissible assignment; reason: the parameter-dependent construction in the proof on p. 15 requires a uniform family rather than an independently chosen constant kernel matrix
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 4.10, p. 14

import Definitions.Def_DenseProdQSAT_Testing_Extension
import Definitions.Def_DenseProdQSAT_Testing_Algebra
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem polynomial_kernel {n k d : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (Φ : Instance n k d) (F X : Finset (Fin n))
    (hXF : X ⊆ Finset.univ \ F) (hX : X.Nonempty) (hXk : X.card ≤ k - 1) :
    ∃ (r : ℕ) (M : Matrix (Fin r) (Config d X)
      (MvPolynomial (AmplitudeIndex d F) ℂ)),
      (∀ a b, ∃ e : ℕ, e ≤ k ∧ (M a b).IsHomogeneous e) ∧
      ∀ ψ : States n d, SatisfiesOn Φ F ψ →
        ExtensionSpace Φ F X ψ = LinearMap.ker (Matrix.toLin'
          (M.map (MvPolynomial.eval (fun a => (RealAmplitudes F ψ a : ℂ))))) := by sorry

end DenseProdQSAT.Testing
